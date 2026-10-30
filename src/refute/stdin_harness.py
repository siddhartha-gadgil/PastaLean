"""CPython side of `pastalean refute` for stdin programs (run as a subprocess, JSON on stdin/stdout).

`generate`: run the program with a `sys.stdin` that writes each line *as it is read*, shaped by how the
reading call site consumes it — `int(input())` gets one integer, `a, b = map(int, input().split())` two,
`list(map(int, input().split()))` as many as the last count read, a bare `input()` a word. The transcript
of a run that ends cleanly is a well-formed input; a run that raises is discarded.

`replay`: run the program on given stdin texts; report stdout and the exception kind, if any.
"""

from __future__ import annotations

import ast
import io
import json
import random
import sys

from harness import Timeout, call_with_deadline  # noqa: E402  (runs with its own directory on sys.path)

STRIP = {"strip", "rstrip", "lstrip"}
WRAPPERS = {"list", "tuple", "sorted", "set", "deque"}


class Unsupported(Exception):
    """The program reads stdin in a way lines cannot be generated for (e.g. `sys.stdin.read()`)."""


def _is_read(node) -> bool:
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if isinstance(f, ast.Name) and f.id == "input":
        return True
    return isinstance(f, ast.Attribute) and f.attr == "readline" and \
        isinstance(f.value, ast.Attribute) and f.value.attr == "stdin"


def _parents(tree):
    up = {}
    for n in ast.walk(tree):
        for c in ast.iter_child_nodes(n):
            up[c] = n
    return up


def _called_as(node, up, attr: str | None = None):
    """The call `node.attr(...)` (or `f(node)` when `attr` is None and `f` is returned instead)."""
    p = up.get(node)
    if attr is not None:
        if isinstance(p, ast.Attribute) and p.attr == attr and isinstance(up.get(p), ast.Call) and up[p].func is p:
            return up[p]
        return None
    if isinstance(p, ast.Call) and node in p.args and isinstance(p.func, ast.Name):
        return p
    return None


def _target_arity(node, up):
    """`k` when `node` is unpacked into exactly `k` names, else `None`."""
    p = up.get(node)
    if isinstance(p, ast.Assign) and len(p.targets) == 1 and isinstance(p.targets[0], (ast.Tuple, ast.List)):
        elts = p.targets[0].elts
        if not any(isinstance(e, ast.Starred) for e in elts):
            return len(elts)
    return None


def shape_of(call, up):
    """How the line read by `call` is consumed: ("int",) / ("float",) / ("word",) / ("tokens", elem, k)."""
    node = call
    while (nxt := next((c for a in STRIP if (c := _called_as(node, up, a))), None)) is not None:
        node = nxt
    split = _called_as(node, up, "split")
    if split is not None:
        node, elem = split, "word"
        p = up.get(node)
        if isinstance(p, ast.Call) and isinstance(p.func, ast.Name) and p.func.id == "map" and len(p.args) == 2 \
                and p.args[1] is node and isinstance(p.args[0], ast.Name):
            elem = {"int": "int", "float": "float"}.get(p.args[0].id, "word")
            node = p
        elif isinstance(p, ast.comprehension) and p.iter is node:
            comp = up.get(p)
            elt = getattr(comp, "elt", None)
            if isinstance(elt, ast.Call) and isinstance(elt.func, ast.Name) and elt.func.id in ("int", "float"):
                elem = elt.func.id
            node = comp
        while (w := _called_as(node, up)) is not None and w.func.id in WRAPPERS:
            node = w
        return ("tokens", elem, _target_arity(node, up))
    w = _called_as(node, up)
    if w is not None and w.func.id in ("int", "float"):
        return (w.func.id,)
    return ("word",)


def shapes(source: str) -> dict[int, list]:
    """The shape of every stdin read, by source line (in column order)."""
    tree = ast.parse(source)
    up = _parents(tree)
    out: dict[int, list] = {}
    for n in ast.walk(tree):
        if _is_read(n):
            out.setdefault(n.lineno, []).append((n.col_offset, shape_of(n, up)))
    return {ln: [s for _, s in sorted(v)] for ln, v in out.items()}


class GenStdin(io.TextIOBase):
    """A stdin that writes each line when it is read, recording the transcript."""

    def __init__(self, table, rng, size, negative):
        self.table, self.rng, self.size, self.negative = table, rng, size, negative
        self.lines: list[str] = []
        self.count: int | None = None   # the last count-like integer read

    def _int(self):
        r = self.rng.random()
        if r < 0.12:
            v = 0
        elif r < 0.9:
            v = self.rng.randint(1, max(1, self.size))
        else:
            v = self.rng.randint(self.size, 3 * self.size + 1)
        return -v if self.negative and self.rng.random() < 0.2 else v

    def _float(self):
        return repr(self.rng.randint(-4 * self.size, 4 * self.size) / 2 ** self.rng.randint(0, 3))

    def _word(self):
        return "".join(self.rng.choice("ab") for _ in range(self.rng.randint(1, max(1, self.size))))

    def _line(self, shape) -> str:
        if shape[0] == "int":
            v = self._int()
            self.count = v
            return str(v)
        if shape[0] == "float":
            return self._float()
        if shape[0] == "word":
            return self._word()
        _, elem, k = shape
        if k is None:
            k = self.count if self.count is not None and 0 <= self.count <= 4 * self.size + 4 \
                else self.rng.randint(0, self.size)
        toks = [str(self._int()) if elem == "int" else self._float() if elem == "float" else self._word()
                for _ in range(k)]
        if elem == "int" and toks and shape[2] is not None:
            # `n, k = …`: a following list is most often `n` long.
            self.count = int(toks[0])
        return " ".join(toks)

    def readline(self, *_):
        frame = sys._getframe(1)
        while frame is not None and frame.f_code.co_filename != "<program>":
            frame = frame.f_back
        shapes_here = self.table.get(frame.f_lineno if frame else -1) or [("word",)]
        line = self._line(shapes_here[0])
        if len(self.lines) > 5000:
            raise Timeout()
        self.lines.append(line)
        return line + "\n"

    def read(self, *_):
        raise Unsupported("sys.stdin.read()")

    def readlines(self, *_):
        raise Unsupported("sys.stdin.readlines()")

    def __iter__(self):
        raise Unsupported("iterating sys.stdin")


class CheckStdin(io.TextIOBase):
    """Replays given lines, checking each against the shape of the call site that reads it: token
    kinds, unpacking arity and (when `strict`) a list as long as the last count read."""

    def __init__(self, text, table, strict):
        self.lines = text.split("\n")
        if self.lines and self.lines[-1] == "":
            self.lines.pop()
        self.table, self.strict = table, strict
        self.pos, self.count, self.violation = 0, None, None

    def _check(self, line, shape):
        toks = line.split()
        if shape[0] in ("int", "float"):
            if len(toks) != 1 or not _is_num(toks[0], shape[0]):
                return f"expected one {shape[0]}"
            if shape[0] == "int":
                self.count = int(toks[0])
            return None
        if shape[0] == "word":
            return None
        _, elem, k = shape
        if elem != "word" and not all(_is_num(t, elem) for t in toks):
            return f"expected {elem}s"
        if k is not None and len(toks) != k:
            return f"expected {k} tokens"
        if k is None and self.strict and self.count is not None and len(toks) != self.count:
            return f"expected {self.count} tokens"
        if k is not None and elem == "int" and toks:
            self.count = int(toks[0])
        return None

    def readline(self, *_):
        if self.pos >= len(self.lines):
            return ""
        line = self.lines[self.pos]
        self.pos += 1
        frame = sys._getframe(1)
        while frame is not None and frame.f_code.co_filename != "<program>":
            frame = frame.f_back
        shape = (self.table.get(frame.f_lineno if frame else -1) or [("word",)])[0]
        if self.violation is None and (why := self._check(line, shape)):
            self.violation = f"line {self.pos}: {why}"
        return line + "\n"

    def read(self, *_):
        raise Unsupported("sys.stdin.read()")

    def readlines(self, *_):
        raise Unsupported("sys.stdin.readlines()")

    def __iter__(self):
        raise Unsupported("iterating sys.stdin")


def _is_num(t, kind):
    try:
        int(t) if kind == "int" else float(t)
        return True
    except ValueError:
        return False


def run(code, stdin, ms):
    """Execute the compiled program as `__main__` with `stdin`; (stdout, exception kind or None)."""
    out = io.StringIO()
    old = sys.stdin, sys.stdout
    sys.stdin, sys.stdout = stdin, out
    exc = None
    try:
        call_with_deadline(lambda: exec(code, {"__name__": "__main__"}), [], ms)  # noqa: S102
    except SystemExit as e:
        if e.code not in (None, 0):
            exc = "SystemExit"
    except Timeout:
        exc = "Timeout"
    except Unsupported:
        raise
    except BaseException as e:  # noqa: BLE001
        exc = type(e).__name__
    finally:
        sys.stdin, sys.stdout = old
    return out.getvalue(), exc


def generate(source, req):
    code = compile(source, "<program>", "exec")
    table = shapes(source)
    rng = random.Random(req.get("seed", 24301))
    n, max_size = req.get("n", 200), req.get("maxSize", 8)
    seen, kept, rejected = set(), [], 0
    for i in range(n * 3):
        if len(kept) >= n:
            break
        size = 1 + (i * max_size) // (n * 3)
        g = GenStdin(table, rng, size, req.get("negative", False))
        try:
            stdout, exc = run(code, g, req.get("ms", 500))
        except Unsupported as e:
            return {"error": f"cannot generate stdin: the program uses {e}"}
        text = "".join(l + "\n" for l in g.lines)
        if exc is not None or text in seen:
            rejected += exc is not None
            continue
        seen.add(text)
        kept.append({"input": text, "stdout": stdout})
    return {"inputs": kept, "rejected": rejected, "shapes": {str(k): v for k, v in table.items()}}


def replay(source, req):
    """Run each input; with `check` ("strict" / "loose") also whether it conforms to the read shapes."""
    code = compile(source, "<program>", "exec")
    table = shapes(source)
    out = []
    for text in req["inputs"]:
        stdin = CheckStdin(text, table, req["check"] == "strict") if req.get("check") else io.StringIO(text)
        try:
            stdout, exc = run(code, stdin, req.get("ms", 1000))
        except Unsupported as e:
            stdout, exc = "", f"Unsupported: {e}"
        out.append({"stdout": stdout, "exc": exc, "violation": getattr(stdin, "violation", None)})
    return {"runs": out}


def main():
    sys.setrecursionlimit(10000)
    req = json.load(sys.stdin)
    fn = {"generate": generate, "replay": replay}[req["mode"]]
    real_stdout = sys.stdout
    res = fn(req["source"], req)
    json.dump(res, real_stdout)


if __name__ == "__main__":
    main()
