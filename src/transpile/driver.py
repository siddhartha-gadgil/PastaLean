import json
import ast
import atexit
import functools
import importlib
import re
from pathlib import Path
import subprocess
import logging

from .node_visitor import *
from .toplevel_state import (
    annotate_main_entrypoint,
    annotate_toplevel_state,
    annotate_if_assigned_names,
)
from .contract_passta import CONTRACT_FUNCS as PASSTA_STAR_MEMBERS
from ..backend import LeanBackendClient
from ..paths import LIBRARIES_DIR, REPO_ROOT

logger = logging.getLogger(__name__)

def get_supported_libraries():
    # Read directory names from the Libraries folder to determine supported libraries
    libraries_path = LIBRARIES_DIR
    if not libraries_path.exists() or not libraries_path.is_dir():
        logger.warning("Libraries directory not found at %s; no libraries will be supported.", libraries_path)
        return set()
    return {f.name for f in libraries_path.iterdir() if f.is_dir()}

SUPPORTED_LIBRARY_IMPORTS = get_supported_libraries()

# Backwards-compatible Python module names for the PASSTA contract shim. The Lean library lives
# under `Libraries/passta`, while Python examples may import `contracts` or `contract_passta`.
LIBRARY_IMPORT_ALIASES = {
    "contracts": "passta",
    "contract_passta": "passta",
}

# Type-only / compile-time modules: they contribute nothing at runtime (their names live in
# annotations, which `annotate_python.py` normalises to builtin generics). They are neither
# library-mapped nor real cross-file Lean modules, so they must be dropped entirely.
TYPE_ONLY_IMPORTS = {"typing", "typing_extensions", "__future__"}

# Numeric lowering mode sent to the Lean backend: "exact" → Python float becomes Lean ℚ
# (provable + computable); "approx" → Float (fast, runnable). Set per backend send.
_NUMERIC_MODE = "exact"
_BEST_EFFORT = False
# Run-twin suffix (`--mode both`): "'rn" while emitting the runnable twin of a declaration, "" for
# the single-version modes. `_USER_NAMES` lists the user functions/classes whose references the
# backend suffixes in a twin (so `foo'rn` calls `bar'rn`, builds `CNN'rn`).
_RUN_SUFFIX = ""
_USER_NAMES = []

# Opt-in reference semantics (`--heap`): when True, class instances and mutable containers become
# heap-allocated refs (real Python aliasing) via the heap monad, instead of value semantics. Set per
# `translate_to_lean` call and sent to the backend on every request.
_HEAP_MODE = False

# Statements the most recent `translate_to_json` degraded to `pyUnsupported(...)` under best-effort.
_LAST_UNSUPPORTED = []

# Submodules of a supported library that act as nested namespaces (e.g. `scipy.special`). Their
# members all flatten into the top-level library's registry, so importing the submodule (e.g.
# `from scipy import special`) binds a *module*-kind name that resolves `special.factorial`.
LIBRARY_SUBMODULES = {
    "scipy": {"special", "constants", "stats", "linalg"},
}


def _supported_library_root(module_name):
    """Top-level package of `module_name` if it (or its root) is a supported library, else None.
    e.g. `scipy.special` -> `scipy`, `numpy` -> `numpy`, `os.path` -> None."""
    if not isinstance(module_name, str) or not module_name:
        return None
    root = module_name.split(".")[0]
    root = LIBRARY_IMPORT_ALIASES.get(root, root)
    return root if root in SUPPORTED_LIBRARY_IMPORTS else None

COMMENT_PLACEHOLDER_RE = re.compile(
    r"^(?P<indent>\s*)(?:let|def)\s+__PastaLean_comment_(?P<id>\d+)\b.*$"
)

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor; all translation logic lives in the base class."""
    pass

def configure_logging(verbose: bool) -> None:
    """Configure CLI logging, keeping normal runs quiet unless verbose is enabled."""
    level = logging.DEBUG if verbose else logging.WARNING
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")


def _node_type(node):
    return node.get("node_type") if isinstance(node, dict) else None


def _walk_json_nodes(node, *, skip_nested_function_bodies=False):
    if isinstance(node, dict):
        yield node
        node_type = node.get("node_type")
        for key, value in node.items():
            if skip_nested_function_bodies and node_type == "FunctionDef" and key == "body":
                continue
            yield from _walk_json_nodes(value, skip_nested_function_bodies=skip_nested_function_bodies)
    elif isinstance(node, list):
        for item in node:
            yield from _walk_json_nodes(item, skip_nested_function_bodies=skip_nested_function_bodies)


def _comment_node_map(node):
    comments = {}
    for subnode in _walk_json_nodes(node):
        node_type = _node_type(subnode)
        if node_type not in {"Comment", "DocString"}:
            continue
        comment_id = subnode.get("comment_id")
        if comment_id is not None:
            comments[str(comment_id)] = subnode
    return comments


def _lean_comment_lines(comment_node, indent):
    text = str(comment_node.get("text", ""))
    if _node_type(comment_node) == "DocString":
        safe_lines = [line.replace("-/", "- /") for line in text.splitlines()] or [""]
        return [f"{indent}/-", *[f"{indent}{line}" for line in safe_lines], f"{indent}-/"]
    body = text.replace("\n", " ").replace("\r", " ").strip()
    return [f"{indent}-- {body}" if body else f"{indent}--"]


def _inject_comments_into_lean(ast_json, lean_code):
    comment_map = _comment_node_map(ast_json)
    if not comment_map:
        return lean_code
    output_lines = []
    for line in lean_code.splitlines():
        match = COMMENT_PLACEHOLDER_RE.match(line)
        if match is None:
            output_lines.append(line)
            continue
        comment_node = comment_map.get(match.group("id"))
        if comment_node is None:
            output_lines.append(line)
            continue
        output_lines.extend(_lean_comment_lines(comment_node, match.group("indent")))
    return "\n".join(output_lines)


def _direct_comment_code(ast_json):
    return "\n".join(_lean_comment_lines(ast_json, ""))


def _join_command_parts(parts):
    """Join generated top-level parts, attaching leading comments to the next part.

    `parts` is a list of `(is_comment, text)`. A comment is followed by a single newline
    so it sits directly above the next declaration; declarations are separated by a blank
    line. This avoids a stray blank line after every comment.
    """
    out = ""
    for is_comment, text in parts:
        if not text:
            continue
        if not out:
            out = text
        elif out.endswith("\n"):
            # Previous part was a comment: glue this part directly beneath it.
            out += text
        else:
            out += "\n\n" + text
        if is_comment:
            out += "\n"
    return out


def _lean_module_path(python_module):
    """Map a dotted Python module path to a Lean module path.

    Lean requires each component of a module path to start uppercase (this is how Lean
    resolves `import` to a file and is enforced by Mathlib's linter). We capitalize the
    first letter of every dotted segment and leave the rest — including underscores —
    intact, so the mapping is deterministic and reversible:
        `mymodule`         -> `Mymodule`
        `pkg.sub_pkg.mod`  -> `Pkg.Sub_pkg.Mod`
    Both the importing and the defining file compute this identically, which matters
    because we translate one file at a time and never see the other.
    """
    segments = [seg for seg in python_module.split(".") if seg]
    capitalized = [seg[:1].upper() + seg[1:] for seg in segments]
    return ".".join(capitalized)


def _crossfile_import_lines(body):
    """Build the Lean `import` lines for non-library cross-file imports.

    Library imports (`math`, `numpy`, ...) are handled by symbol mapping and skipped here.
    Both `import a.b` and `from a.b import f, g` become `import A.B`: a translated module
    emits its definitions at the top level (not inside a per-file namespace), and Lean
    makes a module's top-level definitions globally available after `import` — so no `open`
    is needed and the imported names are already unqualified, matching Python's
    `from ... import`. Private (`_`-prefixed) definitions stay non-importable.

    Imports must appear at the very top of a Lean file, so these lines are assembled into
    the preamble rather than emitted per-statement by the backend.
    """
    import_lines = []
    seen_imports = set()

    def add_import(lean_path):
        if lean_path and lean_path not in seen_imports:
            seen_imports.add(lean_path)
            import_lines.append(f"import {lean_path}")

    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        node_type = stmt.get("node_type")
        if node_type == "Import":
            for alias_node in stmt.get("names", []):
                if not isinstance(alias_node, dict):
                    continue
                module_name = alias_node.get("name")
                if not isinstance(module_name, str):
                    continue
                # Skip library modules (reached as `Libraries.math.…`) and foreign ones (`random`
                # has no Lean module; emitting `import Random` breaks the file).
                top = module_name.split(".")[0]
                if top in SUPPORTED_LIBRARY_IMPORTS or top in TYPE_ONLY_IMPORTS:
                    continue
                if alias_node.get("foreign"):
                    continue
                add_import(_lean_module_path(module_name))
        elif node_type == "ImportFrom":
            module_name = stmt.get("module")
            if not isinstance(module_name, str) or not module_name:
                continue
            if (
                _supported_library_root(module_name) is not None
                or module_name.split(".")[0] in TYPE_ONLY_IMPORTS
                or stmt.get("foreign")
            ):
                continue
            add_import(_lean_module_path(module_name))

    return import_lines


def _collect_scope_function_defs(body):
    """Collect the `FunctionDef` nodes that live in a single Python scope.

    A `def` nested inside an `if`/`for`/`while`/`try`/`with` block is still in the *same*
    scope (those compound statements do not introduce a scope in Python), so effect analysis
    must see it — e.g. the harness wraps bare top-level code under `if __name__ == "__main__":`,
    which nests the program's functions one level deep. We descend through compound statements
    but stop at scope boundaries (`FunctionDef`/`AsyncFunctionDef`/`ClassDef`/`Lambda`), whose
    own bodies form separate scopes handled by recursion.
    """
    found = []

    def walk(node):
        if isinstance(node, dict):
            node_type = node.get("node_type")
            if node_type == "FunctionDef":
                found.append(node)
                return  # separate scope: do not descend into its body
            if node_type in {"AsyncFunctionDef", "ClassDef", "Lambda"}:
                return  # separate scopes, not handled by this collector
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    for stmt in body:
        walk(stmt)
    return found


def _body_has_direct_exception_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) in {"Try", "Raise"}:
                return True
    return False


#: Library modules whose members are `IO` (global mutable state), so a call to one makes its
#: enclosing function IO-effectful exactly as `input()` does. Populated from the Lean registry
#: (`Libraries.ioEffectfulLibraries`) via the `libraryInfo` backend task — the fact is DECLARED by
#: the library, never duplicated here. Empty until the backend is reachable, which is safe: the
#: worst case is a missed effect annotation, the same as before the query existed.
_IO_EFFECTFUL_LIBRARIES: set[str] = set()


def refresh_library_info(client):
    """Pull library facts from the Lean registry once per backend process."""
    global _IO_EFFECTFUL_LIBRARIES
    try:
        info = client.library_info()
    except Exception:  # noqa: BLE001  (a missing enrichment must never break translation)
        return
    names = info.get("ioEffectfulLibraries")
    if isinstance(names, list):
        _IO_EFFECTFUL_LIBRARIES = {n for n in names if isinstance(n, str)}


def _is_io_effectful_library_call(func):
    """A `random.randint(...)`-style call: resolved to a library whose members live in `IO`."""
    return (
        isinstance(func, dict)
        and func.get("library_module") in _IO_EFFECTFUL_LIBRARIES
    )


def _body_has_direct_io_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if _is_io_effectful_library_call(func):
                return True
            if (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
            ):
                func_id = func.get("id")
                # In prove mode, print() is a noop and doesn't count as IO
                if func_id == "input":
                    return True
                elif func_id == "print" and _NUMERIC_MODE != "exact":
                    return True
    return False


def _body_calls_known_functions(body, known_names):
    called = set()
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name":
                func_name = func.get("id")
                if func_name in known_names:
                    called.add(func_name)
    return called


def _annotate_calls(node, effectful_names):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node["effect_mode"] = "except"
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls(value, effectful_names)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls(item, effectful_names)


def _annotate_calls_with_mode(node, effectful_names, effect_mode):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node.setdefault("effect_mode", effect_mode)
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls_with_mode(value, effectful_names, effect_mode)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls_with_mode(item, effectful_names, effect_mode)


def _annotate_direct_io_calls(node):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if _is_io_effectful_library_call(func):
                node.setdefault("effect_mode", "io")
            elif (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
            ):
                func_id = func.get("id")
                # In prove mode, print() is a noop (pyPrintNoop) and doesn't require IO in the type
                # input() and print() always need IO effect marking
                # (even in exact mode where they use PyProofM instead of IO)
                if func_id == "input":
                    node.setdefault("effect_mode", "io")
                elif func_id == "print":
                    node.setdefault("effect_mode", "io")
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_direct_io_calls(value)
    elif isinstance(node, list):
        for item in node:
            _annotate_direct_io_calls(item)


def annotate_exception_effects(module_json):
    """Mark function defs and direct calls that require translated `Except` handling."""
    def annotate_scope(body):
        local_functions = {
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        effectful = {
            name: _body_has_direct_exception_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if effectful[name]:
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(effectful.get(callee, False) for callee in called):
                    effectful[name] = True
                    changed = True

        effectful_names = {name for name, is_effectful in effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if effectful[name]:
                fn["effect_mode"] = "except"
            _annotate_calls(fn.get("body", []), effectful_names)

        _annotate_calls(body, effectful_names)

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def annotate_io_effects(module_json):
    """Mark input/print-bearing function defs and direct calls that require translated `IO` handling."""
    def annotate_scope(body):
        local_functions = {
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        io_effectful = {
            name: _body_has_direct_io_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
            if fn.get("effect_mode") != "except"
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if fn.get("effect_mode") == "except":
                    continue
                if io_effectful.get(name, False):
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(io_effectful.get(callee, False) for callee in called):
                    io_effectful[name] = True
                    changed = True

        io_effectful_names = {name for name, is_effectful in io_effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if fn.get("effect_mode") == "except":
                continue
            if io_effectful.get(name, False):
                fn["effect_mode"] = "io"
            _annotate_direct_io_calls(fn.get("body", []))
            _annotate_calls_with_mode(fn.get("body", []), io_effectful_names, "io")

        _annotate_direct_io_calls(body)
        _annotate_calls_with_mode(body, io_effectful_names, "io")

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def _chain_root(node):
    """The root `Name` id of an attribute/subscript chain (`node.children[i]` -> "node")."""
    if not isinstance(node, dict):
        return None
    nt = node.get("node_type")
    if nt == "Name":
        return node.get("id")
    if nt in ("Attribute", "Subscript"):
        return _chain_root(node.get("value"))
    return None


def _chain_has_attr(node):
    """Whether a chain passes through >=1 `.attr` (so `node.next` counts, `node`/`arr[i]` do not)."""
    if not isinstance(node, dict):
        return False
    nt = node.get("node_type")
    if nt == "Attribute":
        return True
    if nt == "Subscript":
        return _chain_has_attr(node.get("value"))
    return False


def _module_needs_heap(node, advanced=None, mutated=None):
    """Best-effort whole-module detection that a program NEEDS reference (`--heap`) semantics: some
    cursor is BOTH advanced into its own field (`node = node.next` / `node = node.children[i]`) AND has
    that field mutated (`node.next = ...`, `node.children[i] = ...`, `node.cnt += ...`). Value semantics
    copies the cursor, so those writes are silently dropped — the trie / linked-list / tree pattern.
    Conservative: both signals must name the SAME cursor, so `arr[i] = v` or a read-only walk never
    trips it. Returns True iff the advanced-and-mutated cursor sets intersect."""
    top = advanced is None
    if top:
        advanced, mutated = set(), set()
    if isinstance(node, dict):
        nt = node.get("node_type")
        if nt == "Assign":
            tgt, val = node.get("target"), node.get("value")
            tname = tgt.get("id") if isinstance(tgt, dict) and tgt.get("node_type") == "Name" else None
            if tname is not None and _chain_root(val) == tname and _chain_has_attr(val):
                advanced.add(tname)          # cursor ADVANCE `node = node.attr...`
        if nt in ("Assign", "AugAssign"):
            tgt = node.get("target")
            # STRUCTURAL mutation `x.field[i] = ...` (container-element write through a cursor's field,
            # the trie `node.children[idx] = Trie()`). A plain scalar field write (`head.val = v`) is
            # deliberately excluded: value semantics returns a correct result for the linked-list walk
            # that does it, so flagging it would needlessly force the heap tier on a working program.
            if isinstance(tgt, dict) and tgt.get("node_type") == "Subscript" and _chain_has_attr(tgt.get("value")):
                r = _chain_root(tgt)
                if r is not None:
                    mutated.add(r)
        for value in node.values():
            _module_needs_heap(value, advanced, mutated)
    elif isinstance(node, list):
        for item in node:
            _module_needs_heap(item, advanced, mutated)
    if top:
        return bool(advanced & mutated)
    return False


def _node_has_direct_heap_syntax(node):
    """Whether `node` directly uses the heap (`--heap`): a class instantiation (`_class_ctor`), an
    instance-method call (`_receiver_class`), or a container literal. Does not descend into nested
    function bodies (they own their own effects)."""
    if isinstance(node, dict):
        if node.get("_class_ctor") is not None or node.get("_receiver_class") is not None:
            return True
        if node.get("node_type") in ("List", "Dict", "Set"):
            return True
        nt = node.get("node_type")
        for key, value in node.items():
            if nt == "FunctionDef" and key == "body":
                continue
            if _node_has_direct_heap_syntax(value):
                return True
    elif isinstance(node, list):
        return any(_node_has_direct_heap_syntax(item) for item in node)
    return False


def _annotate_heap_calls(node, heap_names):
    """Stamp `_heap_call` on every call to a heap-effectful user function, so codegen awaits it."""
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in heap_names:
                node["_heap_call"] = True
        nt = node.get("node_type")
        for key, value in node.items():
            if nt == "FunctionDef" and key == "body":
                continue
            _annotate_heap_calls(value, heap_names)
    elif isinstance(node, list):
        for item in node:
            _annotate_heap_calls(item, heap_names)


def _function_own_bound_names(fn):
    """Names bound in `fn`'s OWN scope: its parameters plus every name assigned directly in its body.
    Does not descend into nested function bodies — those are separate scopes."""
    names = set(_function_arg_names(fn))
    for stmt in fn.get("body", []):
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if isinstance(node, dict) and node.get("node_type") in {
                "Assign", "AnnAssign", "AugAssign", "For", "FunctionDef", "ClassDef",
            }:
                names |= _stmt_bound_names(node)
    return names


def _body_promotes_variable_cell(fn):
    """Whether `fn` promotes one of its locals to a shared `Ref` CELL under `--heap`: some nested
    closure REBINDS a captured local of `fn` (`nonlocal v; v = …`/`v += …`). Such a var is allocated
    as a cell in `fn`'s body, so `fn` is heap-effectful even with no direct heap syntax of its own —
    mirrors ClosureConvert's mutated-capture promotion. In-place container mutation (`v.append(…)`)
    needs no `nonlocal` and is already caught via the container-literal seed."""
    own_locals = _function_own_bound_names(fn)
    if not own_locals:
        return False
    for stmt in fn.get("body", []):
        for nested in _walk_json_nodes(stmt):
            if not (isinstance(nested, dict) and nested.get("node_type") == "FunctionDef"):
                continue
            nonlocal_names = set()
            for node in _walk_json_nodes(nested.get("body", []), skip_nested_function_bodies=True):
                if isinstance(node, dict) and node.get("node_type") == "Nonlocal":
                    nonlocal_names.update(n for n in node.get("names", []) if isinstance(n, str))
            # Guard against a bare `nonlocal v` (only read, never rebound): that stays a value param,
            # so flagging `fn` heap-effectful would make callers await a non-`HeapM` value.
            rebound = nonlocal_names & _function_own_bound_names(nested)
            if rebound & own_locals:
                return True
    return False


def _collect_module_class_names(module_json):
    """Every user-defined class name in the module (a param annotated with one is a heap object)."""
    names = set()
    for node in _walk_json_nodes(module_json):
        if isinstance(node, dict) and node.get("node_type") == "ClassDef":
            name = node.get("name")
            if isinstance(name, str):
                names.add(name)
    return names


def _function_has_ref_param(fn, class_names):
    """Under `--heap`, whether `fn` takes a parameter passed by `Ref` — a mutable container
    (`list`/`dict`/`set`) or a user object. Such a param makes `fn` heap-tier (its body derefs the
    ref) so its callers must await it. Reads the explicit `annotation` or the inferred `_ty`."""
    args = fn.get("args", {})
    if not isinstance(args, dict):
        return False
    for key in ("posonlyargs", "args", "kwonlyargs"):
        for arg in args.get(key, []):
            if not isinstance(arg, dict):
                continue
            for ann in (arg.get("annotation"), arg.get("_ty")):
                if _is_container_annotation(ann):
                    return True
                if (isinstance(ann, dict) and ann.get("node_type") == "Name"
                        and ann.get("id") in class_names):
                    return True
    return False


def annotate_heap_effects(module_json):
    """Under `--heap`, mark calls to heap-effectful user functions with `_heap_call` (interprocedural
    fixpoint, mirroring `annotate_io_effects`): a function is heap-effectful if its body directly uses
    the heap, promotes a closure cell, takes a container/object (`Ref`) parameter, or (transitively)
    calls a heap-effectful function. Codegen then runs such functions in `HeapM` and awaits their calls."""
    class_names = _collect_module_class_names(module_json)
    def annotate_scope(body):
        local_functions = {
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        heap_effectful = {
            name: _node_has_direct_heap_syntax(fn.get("body", []))
            or _body_promotes_variable_cell(fn)
            or _function_has_ref_param(fn, class_names)
            for name, fn in local_functions.items()
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if heap_effectful.get(name, False):
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(heap_effectful.get(callee, False) for callee in called):
                    heap_effectful[name] = True
                    changed = True

        heap_names = {name for name, is_effectful in heap_effectful.items() if is_effectful}
        for fn in local_functions.values():
            _annotate_heap_calls(fn.get("body", []), heap_names)
        _annotate_heap_calls(body, heap_names)

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def _annotate_container_return_calls(node, names):
    """Stamp `_returns_container` on each call (at this scope level) to a container-returning function."""
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in names:
                node["_returns_container"] = True
        nt = node.get("node_type")
        for key, value in node.items():
            if nt == "FunctionDef" and key == "body":
                continue
            _annotate_container_return_calls(value, names)
    elif isinstance(node, list):
        for item in node:
            _annotate_container_return_calls(item, names)


def annotate_container_returning_calls(module_json):
    """Under `--heap`, stamp `_returns_container` on every call to a user function whose declared
    (`returns`) or inferred (`_ret_ty`) return type is a mutable container. The callee hands back the
    object-ref (`Ref (List …)`), so the caller must treat the result as a container-ref: a bound
    target is registered as a heap container (later `len`/subscript/iterate deref) and inline
    consumption dereferences the call result directly. Scope handling mirrors `annotate_heap_effects`.
    Runs AFTER type inference so unannotated container returns are caught via `_ret_ty`."""
    def _returns_container(fn):
        return _is_container_annotation(fn.get("returns")) or _is_container_annotation(fn.get("_ret_ty"))

    def annotate_scope(body):
        local_functions = {
            fn["name"]: fn
            for fn in _collect_scope_function_defs(body)
            if isinstance(fn.get("name"), str)
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))
        container_returning = {name for name, fn in local_functions.items() if _returns_container(fn)}
        if not container_returning:
            return
        for fn in local_functions.values():
            _annotate_container_return_calls(fn.get("body", []), container_returning)
        _annotate_container_return_calls(body, container_returning)

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


# Library members whose result is a real (irrational) number — they lower to noncomputable `ℝ`
# in exact mode (mirrors `pythonLibraryMapReal?` on the Lean side). A function that (transitively)
# produces one of these can't stay in `ℚ`, so its floats lower to `ℝ` instead.
REAL_TRANSCENDENTAL_MEMBERS = {
    "math": {"sqrt", "exp", "log", "sin", "cos", "tan", "pi", "e"},
    "numpy": {"exp", "log", "log10", "log2", "sqrt", "std"},
    "scipy": {"pi", "gamma", "gmean", "norm"},
}


def _node_uses_transcendental(node):
    module = node.get("library_module")
    member = node.get("library_member")
    return (
        isinstance(module, str)
        and module in REAL_TRANSCENDENTAL_MEMBERS
        and member in REAL_TRANSCENDENTAL_MEMBERS[module]
    )


def _body_uses_transcendental(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if isinstance(node, dict) and _node_uses_transcendental(node):
                return True
    return False


def _iter_function_defs(module_json):
    """Every `FunctionDef` node anywhere in the module (including class methods and nested defs)."""
    return [
        node
        for node in _walk_json_nodes(module_json)
        if isinstance(node, dict) and node.get("node_type") == "FunctionDef"
    ]


def _func_own_body_nodes(fn):
    """All IR nodes in `fn`'s OWN body — does not descend into nested function bodies."""
    for stmt in fn.get("body", []):
        yield from _walk_json_nodes(stmt, skip_nested_function_bodies=True)


def _callee_name(func):
    """The function/method name a `Call.func` refers to: a plain `Name` id, or an `Attribute`'s
    `attr` (so `self.sigmoid(x)` / `obj.m(x)` resolve to method `sigmoid`/`m` by name)."""
    if isinstance(func, dict):
        if func.get("node_type") == "Name":
            return func.get("id"), 0
        if func.get("node_type") == "Attribute":
            return func.get("attr"), 1  # method: args line up after the implicit `self`
    return None, 0


def _self_field_name(target):
    """If `target` writes to `self.<field>` (possibly through subscripts, e.g. `self.w[i] = …`),
    the field name; else `None`. Mutating an element makes the whole field hold the element type."""
    t = target
    while isinstance(t, dict) and t.get("node_type") == "Subscript":
        t = t.get("value")
    if isinstance(t, dict) and t.get("node_type") == "Attribute":
        owner = t.get("value")
        if isinstance(owner, dict) and owner.get("node_type") == "Name" and owner.get("id") == "self":
            return t.get("attr")
    return None


def _assign_base_name(node):
    """The root variable name an Assign/AnnAssign/AugAssign writes to, plus the `Name` target node
    when the target is a plain `Name`. Follows `Subscript`/`Attribute` chains to the root (so
    `w[0] = …` and `w[0][1] = …` both attribute to `w`), since mutating an element makes the whole
    container hold the element's type."""
    target = node.get("target")
    name_node = target if isinstance(target, dict) and target.get("node_type") == "Name" else None
    while isinstance(target, dict) and target.get("node_type") in ("Subscript", "Attribute"):
        target = target.get("value")
    if isinstance(target, dict) and target.get("node_type") == "Name":
        return target.get("id"), name_node
    return None, None


def annotate_real_flow(module_json):
    """Per-VARIABLE real-number dataflow. Marks (in exact mode) exactly the variables/parameters
    that hold an irrational `ℝ` value, so the Lean backend ascribes `ℝ` only to those slots and
    leaves everything else `ℚ`/`Int` (which stays computable + provable). Lean's `ℚ ↪ ℝ` scalar
    coercion bridges a `ℚ` value flowing into an `ℝ` scalar position (call args, `q + sqrt x`).

    Forward monotone fixpoint over a per-`(function, name)` lattice:
      - a variable assigned an expression that is real → real;
      - a call argument that is real → the callee's matching parameter is real (arg→param);
      - a function whose `return` value is real → "returns real", which makes `y = f(…)` real.
    An expression is real if it contains a transcendental member, references a real var/param, or
    calls a function that returns real.

    Stamps: `_real` on real parameter (`arg`) nodes and real assignment targets; `_real_fn` on any
    function/guard that produces or *handles* an `ℝ` (drives `noncomputable`, decoupled from which
    individual floats are `ℝ`)."""
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return

    functions = {}
    for fn in _iter_function_defs(module_json):
        name = fn.get("name")
        if isinstance(name, str):
            functions[name] = fn  # last def wins on a (rare) name collision

    param_names = {
        name: [
            a.get("arg")
            for a in fn.get("args", {}).get("args", [])
            if isinstance(a, dict)
        ]
        for name, fn in functions.items()
    }
    real_names = {name: set() for name in functions}  # real var/param names, per function
    returns_real = {name: False for name in functions}
    real_fields = set()  # instance fields `self.X` that hold an ℝ value (class-global)

    def expr_is_real(expr, scope):
        for node in _walk_json_nodes(expr, skip_nested_function_bodies=True):
            if not isinstance(node, dict):
                continue
            if _node_uses_transcendental(node):
                return True
            node_type = node.get("node_type")
            if node_type == "Name" and node.get("id") in real_names[scope]:
                return True
            if node_type == "Attribute":
                owner = node.get("value")
                if (
                    isinstance(owner, dict)
                    and owner.get("node_type") == "Name"
                    and owner.get("id") == "self"
                    and node.get("attr") in real_fields
                ):
                    return True
            if node_type == "Call":
                callee, _ = _callee_name(node.get("func"))
                if returns_real.get(callee, False):
                    return True
        return False

    changed = True
    while changed:
        changed = False
        for name, fn in functions.items():
            for node in _func_own_body_nodes(fn):
                node_type = node.get("node_type")
                if node_type in ("Assign", "AnnAssign", "AugAssign"):
                    base_name, _ = _assign_base_name(node)
                    value = node.get("value")
                    if (
                        base_name
                        and value is not None
                        and base_name not in real_names[name]
                        and expr_is_real(value, name)
                    ):
                        real_names[name].add(base_name)
                        changed = True
                    field = _self_field_name(node.get("target"))
                    if (
                        field
                        and field not in real_fields
                        and value is not None
                        and expr_is_real(value, name)
                    ):
                        real_fields.add(field)
                        changed = True
                elif node_type == "Call":
                    callee, self_offset = _callee_name(node.get("func"))
                    if callee in functions:
                        for i, arg in enumerate(node.get("args", [])):
                            pi = i + self_offset  # skip the implicit `self` for method calls
                            if pi >= len(param_names[callee]):
                                break
                            pname = param_names[callee][pi]
                            if (
                                pname
                                and pname not in real_names[callee]
                                and expr_is_real(arg, name)
                            ):
                                real_names[callee].add(pname)
                                changed = True
                    # A list-mutating method `xs.append(v)` / `.extend(v)` / `.insert(i, v)` makes
                    # the receiver hold `v`'s type — so a list built by appending real values is real.
                    func = node.get("func")
                    if (
                        isinstance(func, dict)
                        and func.get("node_type") == "Attribute"
                        and func.get("attr") in ("append", "extend", "insert")
                    ):
                        args = node.get("args", [])
                        if args and expr_is_real(args[-1], name):
                            recv = func.get("value")
                            if isinstance(recv, dict) and recv.get("node_type") == "Name":
                                rn = recv.get("id")
                                if rn and rn not in real_names[name]:
                                    real_names[name].add(rn)
                                    changed = True
                            else:
                                fld = _self_field_name(recv)
                                if fld and fld not in real_fields:
                                    real_fields.add(fld)
                                    changed = True
                elif node_type == "Return":
                    value = node.get("value")
                    if (
                        value is not None
                        and not returns_real[name]
                        and expr_is_real(value, name)
                    ):
                        returns_real[name] = True
                        changed = True

    # Stamp the IR with the converged marks.
    for name, fn in functions.items():
        reals = real_names[name]
        for a in fn.get("args", {}).get("args", []):
            if isinstance(a, dict) and a.get("arg") in reals:
                a["_real"] = True
        for node in _func_own_body_nodes(fn):
            node_type = node.get("node_type")
            if node_type in ("Assign", "AnnAssign", "AugAssign"):
                base_name, target_node = _assign_base_name(node)
                value = node.get("value")
                # Stamp EVERY assignment whose root var is real (even a `x = 0.0` whose own RHS
                # isn't real but `x` is real elsewhere), so the RHS is lowered in real-context
                # (literals → `ℝ`, list literals → `List ℝ`); the mutable then infers `ℝ`.
                # ALSO stamp when the RHS itself is real even if the target is not a single Name — a
                # TUPLE-unpack of a real-returning call (`dist, nn = find_nearest_neighbor(...)`): the
                # real-context makes each `float`-typed element `ℝ` (an `int` element is unaffected),
                # so an `ℝ` tuple slot is no longer mis-ascribed `ℚ` (there is no `Coe ℝ ℚ`).
                if (
                    base_name in reals
                    or _self_field_name(node.get("target")) in real_fields
                    or (value is not None and expr_is_real(value, name))
                ):
                    node["_real"] = True
                    if target_node is not None:
                        target_node["_real"] = True
            elif node_type == "Return" and returns_real[name]:
                # The function's return type is `ℝ`; lower every `return` value in real-context so a
                # literal-only branch (e.g. `return -1.0, []`) matches an `ℝ`-valued branch.
                node["_real"] = True

    # `_real_fn` (→ `noncomputable`) — a function is noncomputable if it produces or *handles* an ℝ
    # value, OR calls a `_real_fn` function (cascade through void calls too, e.g. `main` → `train`).
    real_fn = {
        name
        for name, fn in functions.items()
        if real_names[name]
        or returns_real[name]
        or any(expr_is_real(stmt, name) for stmt in fn.get("body", []))
    }
    changed = True
    while changed:
        changed = False
        for name, fn in functions.items():
            if name in real_fn:
                continue
            for node in _func_own_body_nodes(fn):
                if node.get("node_type") == "Call":
                    callee, _ = _callee_name(node.get("func"))
                    if callee in real_fn:
                        real_fn.add(name)
                        changed = True
                        break
    for name in real_fn:
        functions[name]["_real_fn"] = True

    # Stamp `_real` on the structure-field declarations of real instance fields (so the Lean
    # `structure` types them `ℝ`), matching the real-context values written into them.
    for node in _walk_json_nodes(module_json):
        if isinstance(node, dict) and node.get("node_type") == "ClassDef":
            for fld in node.get("fields", []):
                if isinstance(fld, dict) and fld.get("name") in real_fields:
                    fld["_real"] = True

    # The `__main__` guard becomes Lean's `def main`; if it calls a noncomputable (`_real_fn`)
    # function, that wrapper must be `noncomputable` too.
    real_fn_names = {name for name, fn in functions.items() if fn.get("_real_fn")}
    for stmt in module_json.get("body", []):
        if isinstance(stmt, dict) and stmt.get("node_type") == "If":
            guard_body = stmt.get("body", [])
            if _body_uses_transcendental(guard_body) or _body_calls_known_functions(
                guard_body, real_fn_names
            ):
                stmt["_real_fn"] = True


def _imported_alias_name(alias_node):
    asname = alias_node.get("asname")
    if isinstance(asname, str) and asname:
        return asname
    name = alias_node.get("name")
    if not isinstance(name, str) or not name:
        return None
    return name.split(".")[0]


def _stmt_bound_names(node):
    bound = set()
    if not isinstance(node, dict):
        return bound
    node_type = node.get("node_type")
    if node_type == "Name":
        ident = node.get("id")
        if isinstance(ident, str):
            bound.add(ident)
    elif node_type in {"Tuple", "List"}:
        for elt in node.get("elts", []):
            bound.update(_stmt_bound_names(elt))
    elif node_type == "arg":
        ident = node.get("arg")
        if isinstance(ident, str):
            bound.add(ident)
    elif node_type == "Assign":
        # The IR carries a single `target`; `targets` is tolerated for older/multi-target shapes.
        bound.update(_stmt_bound_names(node.get("target")))
        for target in node.get("targets", []):
            bound.update(_stmt_bound_names(target))
    elif node_type == "AnnAssign":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type == "AugAssign":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type == "For":
        bound.update(_stmt_bound_names(node.get("target")))
    elif node_type in {"FunctionDef", "ClassDef"}:
        name = node.get("name")
        if isinstance(name, str):
            bound.add(name)
    return bound


def _function_arg_names(fn_node):
    args = fn_node.get("args", {})
    names = set()
    if not isinstance(args, dict):
        return names
    for key in ("posonlyargs", "args", "kwonlyargs"):
        for arg in args.get(key, []):
            names.update(_stmt_bound_names(arg))
    names.update(_stmt_bound_names(args.get("vararg")))
    names.update(_stmt_bound_names(args.get("kwarg")))
    return names


def _comprehension_target_names(node):
    """Names bound by a comprehension/lambda target (`Name`, or the elements of a tuple/list target)."""
    names = set()
    def walk(n):
        if not isinstance(n, dict):
            return
        if n.get("node_type") == "Name":
            names.add(n.get("id"))
        elif n.get("node_type") in ("Tuple", "List"):
            for elt in n.get("elts", []) or []:
                walk(elt)
    walk(node)
    return names


def _annotate_library_refs_in_expr(node, import_env, shadowed=frozenset()):
    """`shadowed` are names bound LOCALLY (parameters, assignments, comprehension/lambda binders).
    They must not be read as library references even when they happen to share a name with a
    supported library — `def f(string)` makes `string.lower()` a method call, not `string.lower`."""
    if isinstance(node, list):
        for item in node:
            _annotate_library_refs_in_expr(item, import_env, shadowed)
        return
    if not isinstance(node, dict):
        return

    node_type = node.get("node_type")
    # A comprehension/lambda binder is a LOCAL name that SHADOWS any star-imported member of the same
    # name (`[e for e in xs]` / `lambda e: …` under `from math import *` must not rewrite `e` to the
    # math constant). Recurse into the sub-expression with those names removed from the import env.
    if node_type in ("ListComp", "SetComp", "DictComp", "GeneratorExp", "Lambda"):
        bound = set()
        if node_type == "Lambda":
            for arg in (node.get("args", {}) or {}).get("args", []) or []:
                if arg.get("arg"):
                    bound.add(arg.get("arg"))
        else:
            for gen in node.get("generators", []) or []:
                bound |= _comprehension_target_names(gen.get("target"))
        sub_env = {k: v for k, v in import_env.items() if k not in bound} if bound else import_env
        sub_shadowed = (shadowed | bound) if bound else shadowed
        for value in node.values():
            _annotate_library_refs_in_expr(value, sub_env, sub_shadowed)
        return

    if node_type == "Name":
        binding = import_env.get(node.get("id"))
        if binding and binding.get("kind") == "member":
            node["library_module"] = binding["module"]
            node["library_member"] = binding["member"]
    elif node_type == "Attribute":
        value = node.get("value")
        if isinstance(value, dict) and value.get("node_type") == "Name":
            vid = value.get("id")
            binding = import_env.get(vid)
            if binding and binding.get("kind") == "module":
                node["library_module"] = binding["module"]
                node["library_member"] = node.get("attr")
            elif vid in SUPPORTED_LIBRARY_IMPORTS and vid not in shadowed:
                # `bisect.bisect_left(...)`: a supported-library name used as `X.attr` is the MODULE,
                # even if `from bisect import *` also bound `bisect` (the function alias) — the attribute
                # access disambiguates to the module. Clear the receiver's stale member stamp so it is
                # not itself lowered as a library reference.
                node["library_module"] = vid
                node["library_member"] = node.get("attr")
                value.pop("library_module", None)
                value.pop("library_member", None)

    for key, value in node.items():
        if node_type == "FunctionDef" and key == "body":
            continue
        _annotate_library_refs_in_expr(value, import_env, shadowed)


@functools.lru_cache(maxsize=None)
def _library_star_members(root):
    """Public names `from <root> import *` brings into scope, taken from the real Python module so
    the binding set matches CPython. A name the Lean registry lacks still binds, then fails with a
    precise "unsupported member" error rather than as an unresolved Lean identifier."""
    if root == "passta":
        return frozenset(PASSTA_STAR_MEMBERS)
    # `operator` re-exports many builtins (abs, pow, eq, …); `from operator import *` is in every
    # dataset preamble, so binding all of them would SHADOW those builtins corpus-wide. Bind only the
    # members the Lean registry actually maps (the operator-specific/arith/bitwise ones); everything
    # else falls through to its builtin (`abs`, `pow`, …).
    if root == "operator":
        return frozenset({"xor", "or_", "and_", "add", "sub", "mul", "mod", "floordiv"})
    try:
        module = importlib.import_module(root)
    except ImportError:
        return frozenset()
    exported = getattr(module, "__all__", None)
    if exported is None:
        exported = [n for n in dir(module) if not n.startswith("_")]
    # The builtin `pow` is variadic: `pow(b, e, mod)` is modular exponentiation. A library `pow`
    # (e.g. `math.pow`, which is 2-arg and float-only) must never shadow it, or a 3-arg `pow(b, e, mod)`
    # mis-resolves to the 2-arg library function ("Function expected"). Let it fall through to builtin.
    return frozenset(exported) - {"pow"}


def _strip_library_annotation_from_binders(stmt):
    """Un-annotate the binder `Name`s of an assignment/loop target: a binder is a definition, not a
    reference. Without this, `inf = float('inf')` under `from math import *` emits
    `def Libraries.math.pyMathInf`. Loads inside a subscript target (`xs[gcd(a, b)] = v`) stay."""
    def strip(node):
        if not isinstance(node, dict):
            return
        node_type = node.get("node_type")
        if node_type == "Name":
            node.pop("library_module", None)
            node.pop("library_member", None)
        elif node_type in {"Tuple", "List"}:
            for elt in node.get("elts", []):
                strip(elt)

    if stmt.get("node_type") in {"Assign", "AnnAssign", "AugAssign", "For"}:
        strip(stmt.get("target"))
        for target in stmt.get("targets", []) or []:
            strip(target)


def _scope_bound_names(body):
    """Every name bound anywhere in a function body. A name assigned anywhere in a function is local
    for the whole body, so it can never refer to a star-imported member."""
    # `_stmt_bound_names` also yields the id of a bare `Name`, so restrict it to binding statements.
    binding_stmts = {"Assign", "AnnAssign", "AugAssign", "For", "FunctionDef", "ClassDef"}
    names = set()
    stack = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if node.get("node_type") in binding_stmts:
                names |= _stmt_bound_names(node)
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return names


def _annotate_library_imports_in_scope(body, inherited_env=None, shadowed=frozenset()):
    env = dict(inherited_env or {})
    # Locally-bound names in THIS scope shadow same-named libraries for the whole scope (Python
    # binds per-function, not per-statement), so collect them up front.
    shadowed = set(shadowed) | set(_scope_bound_names(body))
    for stmt in body:
        if not isinstance(stmt, dict):
            continue
        node_type = stmt.get("node_type")
        if node_type == "Import":
            for alias_node in stmt.get("names", []):
                if not isinstance(alias_node, dict):
                    continue
                module_name = alias_node.get("name")
                local_name = _imported_alias_name(alias_node)
                root = _supported_library_root(module_name)
                # `import scipy.special as sp` / `import numpy as np`: bind the local name to the
                # top-level library so `sp.factorial` / `np.array` resolve through its registry.
                if root is not None and isinstance(local_name, str):
                    env[local_name] = {"kind": "module", "module": root}
            continue
        if node_type == "ImportFrom":
            module_name = stmt.get("module")
            root = _supported_library_root(module_name)
            if root is not None:
                is_submodule_path = isinstance(module_name, str) and "." in module_name
                for alias_node in stmt.get("names", []):
                    if not isinstance(alias_node, dict):
                        continue
                    member_name = alias_node.get("name")
                    local_name = _imported_alias_name(alias_node)
                    if member_name == "*":
                        # Bind every name the module exports; later local bindings shadow these.
                        for star_member in _library_star_members(root):
                            env[star_member] = {
                                "kind": "member",
                                "module": root,
                                "member": star_member,
                            }
                        continue
                    if isinstance(member_name, str) and isinstance(local_name, str):
                        # `from scipy import special` binds a submodule namespace; `from
                        # scipy.special import factorial` (and `from math import exp`) bind members.
                        if not is_submodule_path and member_name in LIBRARY_SUBMODULES.get(root, set()):
                            env[local_name] = {"kind": "module", "module": root}
                            continue
                        env[local_name] = {
                            "kind": "member",
                            "module": root,
                            "member": member_name,
                        }
            continue

        _annotate_library_refs_in_expr(stmt, env, shadowed)
        _strip_library_annotation_from_binders(stmt)

        # A binding here shadows a star-imported member from now on (`from math import *` then
        # `inf = float('inf')`). Annotate first, so the RHS still sees the old env.
        for bound_name in _stmt_bound_names(stmt):
            env.pop(bound_name, None)

        if node_type == "ClassDef":
            # Class methods are FunctionDefs under "methods"; annotate library refs in each body.
            for method in stmt.get("methods", []):
                if not isinstance(method, dict):
                    continue
                child_env = dict(env)
                for arg_name in _function_arg_names(method):
                    child_env.pop(arg_name, None)
                for local_name in _scope_bound_names(method.get("body", [])):
                    child_env.pop(local_name, None)
                _annotate_library_imports_in_scope(
                    method.get("body", []), child_env,
                    shadowed | set(_function_arg_names(method)))
        elif node_type == "FunctionDef":
            child_env = dict(env)
            for arg_name in _function_arg_names(stmt):
                child_env.pop(arg_name, None)
            for local_name in _scope_bound_names(stmt.get("body", [])):
                child_env.pop(local_name, None)
            _annotate_library_imports_in_scope(
                stmt.get("body", []), child_env,
                shadowed | set(_function_arg_names(stmt)))
        else:
            for body_key in ("body", "orelse", "finalbody"):
                nested = stmt.get(body_key)
                if isinstance(nested, list):
                    _annotate_library_imports_in_scope(nested, dict(env), shadowed)
            for handler in stmt.get("handlers", []):
                if isinstance(handler, dict):
                    _annotate_library_imports_in_scope(handler.get("body", []), dict(env), shadowed)
            for case in stmt.get("cases", []):
                if isinstance(case, dict):
                    _annotate_library_imports_in_scope(case.get("body", []), dict(env), shadowed)

        for bound_name in _stmt_bound_names(stmt):
            env.pop(bound_name, None)


def annotate_library_imports(module_json):
    """Annotate names/attributes that come from imported libraries such as `math`."""
    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        _annotate_library_imports_in_scope(module_json.get("body", []))


# Lean/Mathlib globals brought into scope by `open PastaLean`/`open Libraries`/Mathlib. A user
# top-level `def max(...)` lands in the root namespace alongside core's `max`, so every bare `max`
# call is "ambiguous identifier `max`: [Max.max, max]". We rename such user functions (and their
# references) to a name containing `'` (invalid in Python, so it can never collide with a user name).
_RESERVED_LEAN_GLOBALS = frozenset({"max", "min", "insert", "id", "pred", "succ"})


def _scope_binds_name(funcdef, name):
    """Does this function scope bind `name` locally (a param, or an assignment/for-target anywhere in
    its own body, not descending into nested defs)? If so, `name` inside refers to the local, not the
    module-level function, and must not be renamed."""
    args = funcdef.get("args") or {}
    for key in ("args", "posonlyargs", "kwonlyargs"):
        if any(a.get("arg") == name for a in args.get(key, []) or []):
            return True
    for va in ("vararg", "kwarg"):
        if (args.get(va) or {}).get("arg") == name:
            return True
    for sub in _walk_json_nodes(funcdef.get("body", []), skip_nested_function_bodies=True):
        if sub.get("node_type") == "Name" and sub.get("id") == name \
                and (sub.get("ctx") or {}).get("node_type") == "Store":
            return True
    return False


def _rename_name_refs(node, old, new):
    """Rename every `Name`/`arg` reference `old` -> `new`, but stop descending into a nested function
    scope that rebinds `old` locally (its `old` is a different variable)."""
    if isinstance(node, list):
        for x in node:
            _rename_name_refs(x, old, new)
        return
    if not isinstance(node, dict):
        return
    if node.get("node_type") in ("FunctionDef", "AsyncFunctionDef") and _scope_binds_name(node, old):
        return
    if node.get("node_type") == "Name" and node.get("id") == old:
        node["id"] = new
    for v in node.values():
        _rename_name_refs(v, old, new)


def rename_reserved_shadows(module_json):
    """Rename top-level user functions whose name shadows a Lean/Mathlib global (`max`, `min`, …) so
    calls to them are unambiguous. Only fires when the module actually defines such a function."""
    if not (isinstance(module_json, dict) and module_json.get("node_type") == "Module"):
        return
    body = module_json.get("body", [])
    targets = {
        stmt["name"]: stmt for stmt in body
        if isinstance(stmt, dict)
        and stmt.get("node_type") in ("FunctionDef", "AsyncFunctionDef")
        and stmt.get("name") in _RESERVED_LEAN_GLOBALS
    }
    for old in targets:
        new = f"{old}'usr"
        # A module-level `def max` makes `max` refer to it throughout the module (Python resolves the
        # name at call time), except inside a scope that locally rebinds it — `_rename_name_refs` skips
        # those. The def's own `name` is not a `Name` node, so rename it explicitly.
        targets[old]["name"] = new
        _rename_name_refs(body, old, new)


def _sanitize_hole_identifiers(ast_tree):
    """Rename Python variables whose name is a single underscore when they are *read*.

    Python allows `_` as an ordinary identifier (e.g. `for _ in xs: a = int(_)`), but Lean
    treats a bare `_` as a placeholder/hole, so a read of it elaborates to a metavariable
    rather than the bound value. When `_` is only ever a throwaway binder (`for _ in range(n)`,
    `fun _ => ...`) emitting `_` is correct and idiomatic, so we leave those alone and only
    rewrite when `_` actually appears in a load position somewhere in the module.
    """
    reads_underscore = any(
        isinstance(n, ast.Name) and n.id == "_" and isinstance(n.ctx, ast.Load)
        for n in ast.walk(ast_tree)
    )
    if not reads_underscore:
        return
    safe = "__py_us"
    for n in ast.walk(ast_tree):
        if isinstance(n, ast.Name) and n.id == "_":
            n.id = safe
        elif isinstance(n, ast.arg) and n.arg == "_":
            n.arg = safe


def _local_module_file(root, dotted):
    """Resolve a dotted module name to a local file within `root`: a plain `.py`, a package
    `__init__.py`, or the longest prefix that is a module (the tail being a member). Returns the
    `Path` or None."""
    parts = dotted.split(".")
    p = root.joinpath(*parts)
    if p.with_suffix(".py").is_file():
        return p.with_suffix(".py")
    if (p / "__init__.py").is_file():
        return p / "__init__.py"
    for k in range(len(parts) - 1, 0, -1):
        q = root.joinpath(*parts[:k])
        if q.with_suffix(".py").is_file():
            return q.with_suffix(".py")
        if (q / "__init__.py").is_file():
            return q / "__init__.py"
    return None


def resolve_local_imports(source_code, module_dir):
    """Inline a program's LOCAL imports so single-module inference sees the whole reachable program.

    PastaLean translates each file to its own Lean module, but the `TypeInfer` pass runs per-module,
    so a call to an imported function (`from helper import f; x = f()`) leaves `x` untyped. When the
    imported module is a LOCAL sibling `.py`/package (submodule, `__init__.py`, alias, dotted call —
    all present on disk next to the file), we resolve it here: every reachable module's top-level
    defs are inlined under mangled names and qualified accesses (`mod.f()`, `pkg.sub.f()`, `alias.f()`)
    are rewritten to them, producing one flat self-contained program. Library/foreign imports (numpy,
    random, …) are left untouched. Returns the rewritten source, or None when nothing local resolves.
    """
    if not module_dir:
        return None
    # Fast path: a file with no `import` at all has nothing local to resolve, so skip the parse
    # entirely (this pass otherwise parses the source a second time on top of translate_to_json).
    if "import" not in source_code:
        return None
    root = Path(module_dir)
    try:
        main_tree = ast.parse(source_code)
    except SyntaxError:
        return None

    prepended, module_defs, loading = [], {}, set()

    def mangle(dotted, name):
        return "m_" + dotted.replace(".", "_") + "_" + name

    def resolve_binds(tree, cur_dotted, loader):
        binds = {}
        pkg = cur_dotted.rsplit(".", 1)[0] if "." in cur_dotted else ""
        for node in tree.body:
            if isinstance(node, ast.Import):
                for a in node.names:
                    if _local_module_file(root, a.name):
                        loader(a.name)
                        binds[a.asname or a.name.split(".")[0]] = ("mod", a.name if a.asname else a.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                mod = node.module or ""
                if node.level and pkg:
                    mod = pkg + ("." + mod if mod else "")
                mod_file = _local_module_file(root, mod) if mod else None
                members = loader(mod) if mod_file else {}
                for a in node.names:
                    tgt = members.get(a.name)
                    sub = (mod + "." + a.name) if mod else a.name
                    sub_file = _local_module_file(root, sub)
                    if tgt:
                        binds[a.asname or a.name] = ("name", tgt)
                    # `from pkg import submodule` — only when `pkg.submodule` is a DISTINCT file (not
                    # the same module reached via the prefix fallback, i.e. `name` is a member/const).
                    elif sub_file is not None and sub_file != mod_file:
                        loader(sub)
                        binds[a.asname or a.name] = ("mod", sub)
        return binds

    def load_module(dotted):
        if dotted in module_defs:
            return module_defs[dotted]
        if dotted in loading:
            return {}
        loading.add(dotted)
        f = _local_module_file(root, dotted)
        members = {}
        module_defs[dotted] = members
        if f is None:
            return members
        try:
            tree = ast.parse(f.read_text())
        except SyntaxError:
            return members
        binds = resolve_binds(tree, dotted, load_module)
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                new = mangle(dotted, node.name)
                members[node.name] = new
                node = _rewrite(node, binds)
                node.name = new
                prepended.append(node)
            elif not isinstance(node, (ast.Import, ast.ImportFrom)):
                prepended.append(_rewrite(node, binds))
        return members

    class _Rewriter(ast.NodeTransformer):
        def __init__(self, binds):
            self.binds = binds

        def _chain(self, node):
            parts = []
            while isinstance(node, ast.Attribute):
                parts.append(node.attr); node = node.value
            if isinstance(node, ast.Name):
                parts.append(node.id); return list(reversed(parts))
            return None

        def visit_Attribute(self, node):
            self.generic_visit(node)
            chain = self._chain(node)
            if not chain:
                return node
            head = self.binds.get(chain[0])
            if head is None or head[0] != "mod":
                return node
            modname = head[1]
            for seg in chain[1:-1]:
                modname = modname + "." + seg
            m = load_module(modname).get(chain[-1])
            return ast.copy_location(ast.Name(id=m, ctx=node.ctx), node) if m else node

        def visit_Name(self, node):
            b = self.binds.get(node.id)
            return ast.copy_location(ast.Name(id=b[1], ctx=node.ctx), node) if b and b[0] == "name" else node

    def _rewrite(node, binds):
        return _Rewriter(binds).visit(node)

    main_binds = resolve_binds(main_tree, "__main__", load_module)
    if not main_binds:
        return None
    kept = [_rewrite(n, main_binds) for n in main_tree.body
            if not isinstance(n, (ast.Import, ast.ImportFrom))]
    main_tree.body = prepended + kept
    try:
        return ast.unparse(ast.fix_missing_locations(main_tree))
    except Exception:  # noqa: BLE001
        return None



def translate_to_json(source_code, filepath=None, best_effort=False, infer_only=False,
                      resolve_imports=True):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.

    `infer_only` skips the codegen-only effect passes (exception/IO effects, real-flow, main-guard)
    for the `inferTypes` task, which reads none of them — a ~30% IR-build speedup for the benchmark.

    When `best_effort` is set, unsupported statements (foreign libraries, unhandled syntax) are
    replaced by `pyUnsupported(...)` placeholders instead of aborting; dropped lines are logged
    to stderr.
    """
    # Type annotation is no longer a Python pre-pass: the Lean `TypeInfer` engine infers and stamps
    # types on the IR (`inferTypes` task), so the source is parsed as-is. `filepath` is kept only to
    # resolve cross-file imports (`module_dir` below).
    # Inline LOCAL sibling imports so per-module inference sees the whole reachable program
    # (`from helper import f; x = f()` → `x` typed). Library/foreign imports are left untouched.
    # `resolve_imports=False` is the repo-level path: keep each file a separate module (imports left
    # in the IR) so the Lean `inferRepo` task does all cross-file resolution itself.
    if filepath and resolve_imports:
        _resolved = resolve_local_imports(source_code, str(Path(filepath).resolve().parent))
        if _resolved is not None:
            source_code = _resolved
    logger.debug("Source passed to Python AST parser:\n%s", source_code)
    ast_tree = ast.parse(source_code)
    _sanitize_hole_identifiers(ast_tree)
    logger.debug("Parsed Python AST:\n%s", ast.dump(ast_tree, indent=4))
    module_dir = str(Path(filepath).resolve().parent) if filepath else None
    translator = ASTToJsonLeanVisitor(
        source_code,
        best_effort=best_effort,
        supported_modules=set(SUPPORTED_LIBRARY_IMPORTS) | set(LIBRARY_IMPORT_ALIASES),
        type_only_modules=TYPE_ONLY_IMPORTS,
        module_dir=module_dir,
        infer_only=infer_only,
    )
    data = translator.visit(ast_tree)
    # Record which statements best-effort degraded, so callers (`TranslationResult.unsupported`)
    # can report them instead of having to scrape the log.
    global _LAST_UNSUPPORTED
    _LAST_UNSUPPORTED = list(translator.unsupported_log)
    if best_effort and translator.unsupported_log:
        logger.warning(
            "best-effort: replaced %d unsupported statement(s) with pyUnsupported placeholders:",
            len(translator.unsupported_log),
        )
        for src in translator.unsupported_log:
            logger.warning("  unsupported: %s", src)
    rename_reserved_shadows(data)
    annotate_library_imports(data)          # inference reads library_module/member
    if not infer_only:
        annotate_exception_effects(data)    # codegen effects only — the inferTypes task ignores them
        annotate_io_effects(data)
        annotate_real_flow(data)
        annotate_main_entrypoint(data)
    annotate_toplevel_state(data)
    annotate_if_assigned_names(data)        # inference reads if_assigned_names (hoist ascription)
    if logger.isEnabledFor(logging.DEBUG):
        logger.debug("Generated JSON IR: %s", json.dumps(data))
    return json.dumps(data)

# Process-wide default backend, started lazily on first use. Callers that want an explicit
# lifetime (e.g. `Session`) build their own `LeanBackendClient` and pass it as `client=`.
_LEAN_BACKEND = LeanBackendClient(REPO_ROOT)
atexit.register(_LEAN_BACKEND.close)


def invoke_lean_backend(ast_json, target, check=True, client=None):
    """Send one JSON AST node to the Lean backend and return the parsed JSON response."""
    backend = client or _LEAN_BACKEND
    try:
        return backend.request(
            ast_json,
            target,
            check,
            numeric_mode=_NUMERIC_MODE,
            run_suffix=_RUN_SUFFIX,
            user_names=_USER_NAMES,
            best_effort=_BEST_EFFORT,
            heap=_HEAP_MODE,
        )
    except Exception as err:
        return {"result": False, "error": str(err)}


def _splice_taste_winners(code, winners):
    """Replace each `taste?` proof obligation in `code` with its winning tactic, matched by *byte
    offset*: `winners` is a list of ``{"pos": <byte offset into code>, "proof": <tactic>}``. Matching
    by position (not append order) is essential — a `mvcgen … with taste?` whose VCs `mvcgen` itself
    discharged records NO winner, so order-based zipping would shift every later token onto the wrong
    proof. A token with a matching winner gets it (prettified); a `with taste?` with no winner is a
    self-closed `mvcgen` → drop the dead `with` clause; any other unmatched `taste?` → `sorry`.

    Comment/string aware: `taste?` ALSO shows up inside docstrings/comments (e.g. ``:= by taste?`` in
    prose), which aren't elaborated and have no winner. Those never match a `pos`, so they're left
    untouched — we only substitute `taste?` in actual code (outside `--` line comments, nestable
    `/- -/` block comments, and `"..."` string literals)."""
    by_pos = {w["pos"]: w["proof"] for w in winners if isinstance(w, dict) and "pos" in w}
    out = []
    i, n = 0, len(code)
    in_line_comment = False
    block_depth = 0
    in_string = False
    while i < n:
        two = code[i:i + 2]
        c = code[i]
        if in_line_comment:
            out.append(c)
            i += 1
            if c == "\n":
                in_line_comment = False
            continue
        if block_depth > 0:
            if two == "/-":
                block_depth += 1
                out.append(two)
                i += 2
                continue
            if two == "-/":
                block_depth -= 1
                out.append(two)
                i += 2
                continue
            out.append(c)
            i += 1
            continue
        if in_string:
            if c == "\\" and i + 1 < n:
                out.append(code[i:i + 2])
                i += 2
                continue
            if c == '"':
                in_string = False
            out.append(c)
            i += 1
            continue
        # normal code context
        if two == "--":
            in_line_comment = True
            out.append(two)
            i += 2
            continue
        if two == "/-":
            block_depth = 1
            out.append(two)
            i += 2
            continue
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if code.startswith("taste?", i):
            # Byte offset of this token into `code` (the winners' `pos` is byte-based, UTF-8).
            off = len(code[:i].encode("utf-8"))
            if off in by_pos:
                proof = by_pos[off]
                if proof.strip():
                    # The recorded `c₁; c₂; …` sequence — drop it in verbatim (no `first`, no merge).
                    out.append(proof)
                else:
                    # Empty proof: `mvcgen` discharged every VC, so the trailing `taste?` ran on no
                    # goals. Prune the dangling `taste?` line for a clean `mvcgen [...]`.
                    while out and out[-1].strip() == "":
                        out.pop()
            else:
                # Unmatched `taste?` (e.g. inside prose, or no recorded proof) → keep it compiling.
                out.append("sorry")
            i += len("taste?")
            continue
        out.append(c)
        i += 1
    return "".join(out)

def _newline_before_mvcgen_with(code):
    """Put a contract spec's `mvcgen … invariants` closer on its own line: the pretty-printer glues
    `with <closer>` straight onto the last `⌜…⌝` invariant bullet (rendering `…⌝with taste?`), which
    reads poorly. Break before `with` and align it under `mvcgen` (two spaces). Only the spec
    theorems emit `⌝` immediately followed by `with`, so this can't touch anything else."""
    return re.sub(r"⌝[^\S\n]*with\b", "⌝\n  with", code)


def _references_name(node, target):
    """Recursively check whether a JSON subtree references a `Name` with id `target`."""
    if isinstance(node, dict):
        if node.get("node_type") == "Name" and node.get("id") == target:
            return True
        return any(_references_name(v, target) for v in node.values())
    if isinstance(node, list):
        return any(_references_name(x, target) for x in node)
    return False


def _mutual_recursion_groups(body):
    """Map each top-level function name to its mutual-recursion group (a strongly-connected
    component of the call graph). Singletons are self- or non-recursive; groups of size >= 2 are
    mutually recursive and must be emitted together inside a Lean `mutual … end` block.

    The backend translates one top-level statement at a time, so it never sees two functions
    together; this whole-module analysis lives here and drives sending a group as one `Module`."""
    funcs = [
        (s.get("name"), s)
        for s in body
        if isinstance(s, dict) and s.get("node_type") == "FunctionDef" and isinstance(s.get("name"), str)
    ]
    names = [n for n, _ in funcs]
    reach = {n: {m for m in names if _references_name(b, m)} for n, b in funcs}
    # Transitive closure of "references".
    changed = True
    while changed:
        changed = False
        for n in names:
            for r in list(reach[n]):
                extra = reach.get(r, set()) - reach[n]
                if extra:
                    reach[n] |= extra
                    changed = True
    # SCC of n = every m that n reaches and that reaches n back.
    return {
        n: frozenset([n] + [m for m in reach[n] if m != n and n in reach.get(m, set())])
        for n in names
    }


def _collect_class_table(body):
    """Build {class_name: {methods, mutators, fields, bases}} from the module's ClassDefs, folding
    a single base class's members into each subclass (so inherited methods dispatch correctly)."""
    table = {}
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            table[s["name"]] = {
                "methods": set(m.get("name") for m in s.get("methods", [])),
                "mutators": set(s.get("mutators", [])),
                "value_mutators": set(s.get("value_mutators", [])),
                "fields": set(f.get("name") for f in s.get("fields", [])),
                "statics": set(s.get("staticmethods", [])) | set(s.get("classmethods", [])),
                "bases": [b.get("id") for b in s.get("bases", []) if isinstance(b, dict)],
            }
    for info in table.values():
        for base in info["bases"]:
            if base in table:
                info["methods"] |= table[base]["methods"]
                info["mutators"] |= table[base]["mutators"]
                info["value_mutators"] |= table[base]["value_mutators"]
                info["fields"] |= table[base]["fields"]
    return table


def _prune_inherited_fields(body):
    """Drop a subclass ClassDef's fields that are already declared by its base, so the emitted Lean
    `structure Sub extends Base` does not redeclare an inherited field (which Lean rejects)."""
    own = {}
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            own[s["name"]] = {f.get("name") for f in s.get("fields", [])}
            own[s["name"]] |= set()  # ensure a set even with no fields
    # Transitive base-field set per class (single inheritance).
    bases = {
        s["name"]: [b.get("id") for b in s.get("bases", []) if isinstance(b, dict)]
        for s in body
        if isinstance(s, dict) and s.get("node_type") == "ClassDef"
    }
    def base_fields(name, seen=None):
        seen = seen or set()
        acc = set()
        for base in bases.get(name, []):
            if base in own and base not in seen:
                seen.add(base)
                acc |= own[base] | base_fields(base, seen)
        return acc
    for s in body:
        if isinstance(s, dict) and s.get("node_type") == "ClassDef":
            inherited = base_fields(s["name"])
            if inherited:
                s["fields"] = [f for f in s.get("fields", []) if f.get("name") not in inherited]


def _method_owner_index(table):
    """Map a method name to its class when exactly one class declares it (ambiguous names omitted).
    Used to resolve a method-call receiver's class when its variable type is otherwise unknown."""
    owners = {}
    for cname, info in table.items():
        for m in info["methods"]:
            owners.setdefault(m, set()).add(cname)
    return {m: next(iter(cs)) for m, cs in owners.items() if len(cs) == 1}


def _stamp_class_dispatch(ast_json):
    """Annotate Call nodes with class-dispatch hints so the Lean backend (which sees one statement
    at a time, with no shared state) can lower them deterministically:
      * instantiation `C(..)`  -> `_class_ctor: "C"`
      * method call `obj.m(..)` -> `_receiver_class: "C"`, `_is_mutator: bool`
    Receiver class is resolved from `self` (the enclosing class), tracked `x = C(..)` bindings,
    typed parameters, or a method name unique to one class."""
    if ast_json.get("node_type") != "Module":
        return ast_json
    body = ast_json.get("body", [])
    table = _collect_class_table(body)
    if not table:
        return ast_json
    _prune_inherited_fields(body)
    owners = _method_owner_index(table)

    def ctor_class_of(func, current_class):
        if isinstance(func, dict) and func.get("node_type") == "Name":
            fid = func.get("id")
            if fid in table:
                return fid
            if fid == "cls" and current_class:
                return current_class
        return None

    def receiver_class_of(recv, scope, current_class, method):
        if isinstance(recv, dict) and recv.get("node_type") == "Name":
            rid = recv.get("id")
            if rid == "self" and current_class:
                return current_class
            if rid in scope:
                return scope[rid]
        if method in owners:
            return owners[method]
        return None

    def walk_expr(node, scope, current_class):
        """Stamp Calls anywhere inside an expression (scope is read-only here)."""
        if isinstance(node, list):
            for x in node:
                walk_expr(x, scope, current_class)
            return
        if not isinstance(node, dict):
            return
        if node.get("node_type") == "Call":
            func = node.get("func")
            cls = ctor_class_of(func, current_class)
            if cls is not None:
                node["_class_ctor"] = cls
            elif isinstance(func, dict) and func.get("node_type") == "Attribute":
                method = func.get("attr")
                recv = func.get("value")
                # `ClassName.method(...)` (static, classmethod, or an unbound call passing an
                # explicit instance) calls `C.method` directly without prepending a receiver.
                if (isinstance(recv, dict) and recv.get("node_type") == "Name"
                        and recv.get("id") in table
                        and method in table[recv["id"]]["methods"]):
                    node["_static_class"] = recv["id"]
                else:
                    rcls = receiver_class_of(recv, scope, current_class, method)
                    if rcls is not None and method in table.get(rcls, {}).get("methods", set()):
                        node["_receiver_class"] = rcls
                        node["_is_mutator"] = method in table[rcls]["mutators"]
                        node["_is_value_mutator"] = method in table[rcls]["value_mutators"]
        for v in node.values():
            walk_expr(v, scope, current_class)

    def param_scope(funcdef):
        """Seed a function scope with parameters whose annotation names a known class."""
        sc = {}
        args = (funcdef.get("args") or {}).get("args", [])
        for a in args:
            ann = a.get("annotation")
            if isinstance(ann, dict) and ann.get("node_type") == "Name" and ann.get("id") in table:
                sc[a.get("arg")] = ann["id"]
        return sc

    def walk_stmts(stmts, scope, current_class):
        for stmt in stmts:
            if not isinstance(stmt, dict):
                continue
            nt = stmt.get("node_type")
            if nt == "ClassDef":
                cname = stmt.get("name")
                for m in stmt.get("methods", []):
                    msc = param_scope(m)
                    walk_stmts(m.get("body", []), msc, cname)
                continue
            if nt in ("FunctionDef", "AsyncFunctionDef"):
                walk_stmts(stmt.get("body", []), param_scope(stmt), current_class)
                continue
            # Stamp every expression in the statement, then learn `x = C(..)` bindings.
            walk_expr(stmt, scope, current_class)
            if nt == "Assign":
                target = stmt.get("target")
                value = stmt.get("value")
                if (isinstance(target, dict) and target.get("node_type") == "Name"
                        and isinstance(value, dict) and value.get("node_type") == "Call"):
                    cls = ctor_class_of(value.get("func"), current_class)
                    if cls is not None:
                        scope[target["id"]] = cls
            # Recurse into compound-statement blocks (their bodies share this scope).
            for block_attr in ("body", "orelse", "finalbody"):
                blk = stmt.get(block_attr)
                if isinstance(blk, list):
                    walk_stmts(blk, scope, current_class)
            for handler in stmt.get("handlers", []) or []:
                if isinstance(handler, dict):
                    walk_stmts(handler.get("body", []), scope, current_class)

    walk_stmts(body, {}, None)
    return ast_json


def _lean_ident(name):
    """A safe Lean identifier from a Python name, or None if unusable."""
    return name if isinstance(name, str) and name.isidentifier() else None


def _backend_placeholder_command(stmt, idx, suffix=""):
    """Best-effort placeholder for a top-level statement the *Lean backend* could not translate
    (e.g. a `with` statement, which `node_visitor` emits IR for but the backend has no generator
    for, so it slips past the node-level fallback). Keeps the declaration's name where possible so
    references still resolve; the linter flags the `pyUnsupported` use.

    `suffix` is the run-twin suffix (`'rn`) for this pass, appended to the declared name so the twin
    calling this def still resolves it (e.g. `main'` -> `main''rn`)."""
    node_type = stmt.get("node_type", "statement") if isinstance(stmt, dict) else "statement"
    name = stmt.get("name") if isinstance(stmt, dict) else None
    msg = f"unsupported {node_type} (backend could not translate)"
    # The main entry-point body (`main'`) is awaited by the `main` wrapper, so it must stay a
    # runnable `IO Unit` — a `pyUnsupported` *value* there would dangle the wrapper's reference.
    if name in ("main", "main'"):
        return f'def {name}{suffix} : IO Unit := do\n  let _ := pyUnsupported "{msg}"\n  pure ()'
    ident = _lean_ident(name) or f"__py_unsup_backend_{idx}"
    return f'def {ident}{suffix} := pyUnsupported "{msg}"'


def _collect_user_names(body):
    """The user's module-scope function/class names — references to these get the `'rn` suffix in a
    run-twin (so `foo'rn` calls `bar'rn`, builds `CNN'rn`). NESTED functions (`def` inside `def`) are
    emitted as local `let` bindings regenerated in each twin, so their names must NOT be suffixed."""
    names = set()

    def walk(node):
        if isinstance(node, dict):
            nt = node.get("node_type")
            if nt in ("FunctionDef", "ClassDef"):
                n = node.get("name")
                if isinstance(n, str):
                    names.add(n)
                return  # a def/class boundary: its own body is a separate scope (nested = local)
            if nt in ("AsyncFunctionDef", "Lambda"):
                return
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for it in node:
                walk(it)

    for stmt in body:
        walk(stmt)
    return sorted(names)


# Annotation heads (a `Subscript` value id) that denote a mutable container, for `--heap` universe
# collection. `tuple` is intentionally excluded — Python tuples are immutable value types.
_CONTAINER_ANN_HEADS = {
    "list", "List", "Sequence", "MutableSequence",
    "dict", "Dict", "Mapping", "MutableMapping",
    "set", "Set", "frozenset", "FrozenSet",
}


def _is_container_annotation(ann):
    """True when `ann` is a `list[...]`/`dict[...]`/`set[...]` annotation node."""
    if not isinstance(ann, dict) or ann.get("node_type") != "Subscript":
        return False
    val = ann.get("value")
    return isinstance(val, dict) and val.get("node_type") == "Name" and val.get("id") in _CONTAINER_ANN_HEADS


def _collect_container_annotations(node, acc=None, seen=None):
    """Every distinct mutable-container annotation node reachable in the (type-stamped) AST — from
    inferred `_ty` binder stamps, explicit `annotation`s, and inferred `_ret_ty`. Used by `--heap` to
    build a `Val` constructor per container type, including for local variables (not just fields)."""
    if acc is None:
        acc, seen = [], set()
    if isinstance(node, dict):
        for key in ("_ty", "annotation", "_ret_ty"):
            ann = node.get(key)
            if _is_container_annotation(ann):
                marker = json.dumps(ann, sort_keys=True)
                if marker not in seen:
                    seen.add(marker)
                    acc.append(ann)
        for value in node.values():
            _collect_container_annotations(value, acc, seen)
    elif isinstance(node, list):
        for item in node:
            _collect_container_annotations(item, acc, seen)
    return acc


def translate_to_lean(source_code, target="term", filepath = None, imports_add = True, best_effort=False, mode="both", prove_asserts=False, heap=False, client=None):
    """Translate Python source to Lean via JSON IR and the Lean backend executable.

    `mode` selects the numeric semantics: "prove" (exact ℚ/ℝ, provable), "run" (Float, runnable), or
    "both" (default) — emit the provable version AND a runnable twin whose top-level defs/classes and
    the entry point are suffixed `'rn`, adjacently.

    `client` is the `LeanBackendClient` to translate through; defaults to the process-wide one. Pass
    an explicit client to reuse a single warm Lean process across many files."""
    global _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES, _BEST_EFFORT, _HEAP_MODE
    _NUMERIC_MODE = "approx" if mode == "run" else "exact"
    _BEST_EFFORT = best_effort
    _RUN_SUFFIX, _USER_NAMES = "", []
    json_ir = translate_to_json(source_code, filepath, best_effort=best_effort)
    ast_json = json.loads(json_ir)
    # Reference (`--heap`) semantics are opt-in only. `_module_needs_heap` is kept as a discovery tool
    # (a caller/harness can pass `heap=True` for the trie/linked-list problems it flags), but it never
    # flips the mode on its own: auto-enabling surprised value-semantics programs.
    _HEAP_MODE = heap
    _stamp_class_dispatch(ast_json)
    client = client or _LEAN_BACKEND

    # Whole-module type inference (best-effort): stamp `_ty` using interprocedural flow before the
    # per-statement translate loop, which cannot see across functions. Ferries JSON only — the
    # inference logic lives in Lean (`TypeInfer.inferModule`). On any failure the AST is unchanged.
    if ast_json.get("node_type") == "Module":
        ast_json = client.infer_types(ast_json)
        if heap:
            # Heap-effect propagation runs AFTER class dispatch (keys off `_class_ctor`/`_receiver_class`)
            # AND after inference, so a param inferred (`_ty`) — not just annotated — to be a container/
            # object is seen, matching the Lean side's ref-typing. Stamps `_heap_call` on calls to
            # heap-effectful user functions so they are awaited.
            annotate_heap_effects(ast_json)
            # Post-inference (so inferred `_ret_ty` is available): stamp calls whose callee returns a
            # mutable container, so the caller dereferences the returned object-ref.
            annotate_container_returning_calls(ast_json)

    if ast_json.get("node_type") == "Module":
        body = ast_json.get("body", [])
        # Under --heap, prepend a HeapPrelude node carrying the module's classes. It emits every
        # class `structure`, the per-program `Val` universe, and the `Storable`/`derive_storable%`
        # instances — all of which must precede the class members and functions that reference them.
        if heap and target == "command":
            classes = [s for s in body if isinstance(s, dict) and s.get("node_type") == "ClassDef"]
            # Collect every mutable-container type used anywhere (from inferred `_ty` stamps and
            # annotations), so local list/dict/set variables — not just class fields — get a `Val`
            # constructor. Inject the prelude when the program has classes OR uses any container OR
            # promotes a closure-captured scalar to a cell (`nonlocal n; n += k` allocates `Ref n`,
            # which needs the `Val` universe even when nothing else touches the heap).
            container_types = _collect_container_annotations(ast_json)
            promotes_cell = any(
                _body_promotes_variable_cell(fn) for fn in _iter_function_defs(ast_json)
            )
            if classes or container_types or promotes_cell:
                # In `both` mode the prelude renders the exact AND the runnable `'rn` twin of every
                # struct / `Val` constructor / `Storable` into one `Val` (the prelude is not itself
                # twinned by `node_passes`, so it must emit both halves in a single pass).
                body = [{"node_type": "HeapPrelude", "classes": classes,
                         "container_types": container_types,
                         "emit_twin": mode == "both"}] + body
                ast_json["body"] = body
        user_names = _collect_user_names(body)
        code_key = f"lean_{target}"
        single = "approx" if mode == "run" else "exact"

        def node_passes(node):
            """Emission passes for one top-level node: (numericMode, runSuffix, userNames). In `both`
            mode only definitions/classes and the `__main__` guard get a runnable `'rn` twin (their
            names are suffixed); top-level constants/`del`/statements emit once (an unsuffixed twin
            would just redeclare the same global). `userNames` is passed on EVERY pass (not just the
            twin): it is what tells codegen a name is user-defined so a call to it can be
            `_root_`-qualified against Mathlib clashes; suffixing stays gated on the (empty-here)
            run suffix, so this does not suffix anything outside the twin."""
            nt = node.get("node_type")
            twinnable = nt in ("FunctionDef", "ClassDef", "Module") or (nt == "If" and node.get("is_main_guard"))
            if mode == "both" and twinnable:
                return [("exact", "", user_names), ("approx", "'rn", user_names)]
            return [(single, "", user_names)]

        last_backend_error = {"msg": None}

        def send_node(node):
            """Send `node` once per pass; return the list of code strings, or None on failure
            (stashing the backend's error in `last_backend_error`)."""
            global _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES
            codes = []
            for nmode, suffix, unames in node_passes(node):
                _NUMERIC_MODE, _RUN_SUFFIX, _USER_NAMES = nmode, suffix, unames
                r = invoke_lean_backend(node, target, check=False, client=client)
                if r.get("result") is False or code_key not in r:
                    last_backend_error["msg"] = r.get("error")
                    return None
                codes.append(r[code_key])
            return codes

        def backend_placeholders(node):
            """A `pyUnsupported` placeholder for EACH emission pass (prove + run twin), so a
            degraded twinnable def still declares both `foo` and `foo'rn` — otherwise the run
            twin's references to `foo'rn` dangle."""
            parts = [
                _backend_placeholder_command(node, backend_unsup, suffix)
                for _nmode, suffix, _unames in node_passes(node)
            ]
            return "\n\n".join(parts)

        if target == "command":
            # Each part is (is_comment, text). Standalone comments attach to the next
            # part with a single newline so they read as leading comments, while real
            # declarations are separated by a blank line.
            code_parts = []
            mutual_groups = _mutual_recursion_groups(body)
            emitted_funcs = set()
            backend_unsup = 0
            func_by_name = {
                s.get("name"): s for s in body
                if isinstance(s, dict) and s.get("node_type") == "FunctionDef"
                and isinstance(s.get("name"), str)
            }

            def emit_function_group(name):
                """Emit `name`'s function — or its whole mutual group as one `Module` (→ a Lean
                `mutual … end`) — but first emit any callee functions it references that are not yet
                emitted. Python binds top-level `def`s lazily, so a function may call one defined
                later in the file; Lean needs the callee to precede the caller, so callees are pulled
                forward here (depth-first over the call DAG). Returns an error dict on a hard
                (non-best-effort) backend failure, else None."""
                nonlocal backend_unsup
                if name in emitted_funcs:
                    return None
                group = mutual_groups.get(name, frozenset([name]))
                callees = set()
                for m in group:
                    fn = func_by_name.get(m)
                    if fn is not None:
                        callees |= _body_calls_known_functions(fn.get("body", []), func_by_name.keys())
                for c in sorted(callees):
                    if c not in group and c not in emitted_funcs:
                        err = emit_function_group(c)
                        if err is not None:
                            return err
                if name in emitted_funcs:
                    return None
                stmt = func_by_name[name]
                if len(group) >= 2:
                    members = [
                        s for s in body
                        if isinstance(s, dict) and s.get("node_type") == "FunctionDef"
                        and s.get("name") in group
                    ]
                    module_node = {"node_type": "Module", "body": members}
                    codes = send_node(module_node)
                    if codes is None:
                        if best_effort:
                            logger.warning("best-effort: backend could not translate %s; replaced with pyUnsupported placeholder", name)
                            code_parts.append((False, backend_placeholders(stmt)))
                            backend_unsup += 1
                            emitted_funcs.update(group)
                            return None
                        detail = last_backend_error["msg"]
                        return {"result": False, "error": f"backend could not translate {name}" + (f": {detail}" if detail else "")}
                    for c in codes:
                        code_parts.append((False, c))
                    emitted_funcs.update(group)
                    return None
                codes = send_node(stmt)
                if codes is None:
                    if best_effort:
                        logger.warning("best-effort: backend could not translate a %s; replaced with pyUnsupported placeholder", stmt.get("node_type"))
                        code_parts.append((False, backend_placeholders(stmt)))
                        backend_unsup += 1
                        emitted_funcs.add(name)
                        return None
                    detail = last_backend_error["msg"]
                    return {"result": False, "error": f"backend could not translate {stmt.get('node_type')}" + (f": {detail}" if detail else "")}
                for c in codes:
                    code_parts.append((False, _inject_comments_into_lean(stmt, c)))
                emitted_funcs.add(name)
                return None

            for stmt in body:
                # A top-level Python `pass` is a true no-op, so there is no Lean command to emit.
                if stmt.get("node_type") in {"Pass", "Import", "ImportFrom"}:
                    continue
                if stmt.get("node_type") in {"Comment", "DocString"}:
                    code_parts.append((True, _direct_comment_code(stmt)))
                    continue
                if stmt.get("node_type") == "FunctionDef" and stmt.get("name") in func_by_name:
                    if stmt.get("name") in emitted_funcs:
                        continue
                    err = emit_function_group(stmt.get("name"))
                    if err is not None:
                        return err
                    continue
                codes = send_node(stmt)
                if codes is None:
                    if best_effort:
                        logger.warning("best-effort: backend could not translate a %s; replaced with pyUnsupported placeholder", stmt.get("node_type"))
                        code_parts.append((False, backend_placeholders(stmt)))
                        backend_unsup += 1
                        continue
                    detail = last_backend_error["msg"]
                    return {"result": False, "error": f"backend could not translate {stmt.get('node_type')}" + (f": {detail}" if detail else "")}
                # Inline comment placeholders live inside each emitted version, so inject into the
                # prove version AND every `'rn` twin.
                for c in codes:
                    code_parts.append((False, _inject_comments_into_lean(stmt, c)))

            body_code = _join_command_parts(code_parts)
            if imports_add:
                # Every `import` must precede the first command in a Lean file. We list the
                # runtime imports, then the user's cross-file modules, then the `open`s.
                crossfile_imports = _crossfile_import_lines(body)
                # Heartbeats are the ONLY backstop against a non-terminating elaboration. A closed
                # program over reducible library fns can loop the elaborator (the "closed-program
                # kernel hang"); `maxHeartbeats 0` (unbounded) turns that into an infinite hang that
                # blocks the whole batch/overnight run. The limit is PER-DECLARATION, so a finite cap
                # never penalises large programs — it only fails a genuinely looping declaration.
                # NEVER 0: a bare def gets Lean's default (200000); proving gets 4× headroom for
                # `taste?`/`mvcgen` search.
                proving = "taste?" in body_code or "theorem " in body_code
                heartbeats = 800000 if proving else 200000
                preamble_lines = [
                    "import PastaLean",
                    "import Libraries",
                    "import Std.Tactic.Do",
                    *crossfile_imports,
                    "",
                    "open PastaLean",
                    "open Libraries",
                    "open Std.Do",
                    "",
                    "set_option linter.all false", # shut up warnings which annoyingly popup in output
                    "set_option mvcgen.warning false",
                    "",
                    f"set_option maxHeartbeats {heartbeats}",
                    "",
                    # User code lives in a dedicated namespace so a `def compare`/`def unique` resolves
                    # to the user's own definition (namespace precedence) instead of clashing with the
                    # Lean/Mathlib global of the same name — replacing the old `_root_`-qualification.
                    # `Root` is the placeholder for a single file; multi-file conversion uses
                    # `PastaLean.User.<Dir>.<File>`. PastaBench renames this placeholder to its
                    # per-problem namespace (no nesting).
                    "namespace PastaLean.User.Root",
                    "\n",
                ]
                full_code = "\n".join(preamble_lines) + body_code + "\n\nend PastaLean.User.Root\n"
            else:
                full_code = body_code
            # Lay an `mvcgen … invariants` spec's `with` closer on its own line (cosmetic), for both
            # the spliced and the `--leave-taste` forms.
            full_code = _newline_before_mvcgen_with(full_code)
            # Prove-and-replace pass: elaborate the assembled file in the warm backend so `taste?`
            # searches each assert, then splice the concrete winning tactic (or `sorry`) over each
            # `taste?`. Non-destructive — on any failure we leave the `taste?` obligations in place.
            if prove_asserts and "taste?" in full_code:
                resp = client.prove_file(full_code)
                if resp and resp.get("result") and isinstance(resp.get("winners"), list):
                    full_code = _splice_taste_winners(full_code, resp["winners"])
                    if resp.get("hasErrors"):
                        logger.warning("proveFile reported elaboration errors; some asserts may be left `sorry`.")
                else:
                    logger.warning("proveFile pass unavailable/failed; leaving `taste?` obligations in place.")
            return {"result": True, f"lean_{target}": full_code}

        if len(body) == 1:
            result = invoke_lean_backend(body[0], target, client=client)
            if result.get("result") is False:
                return result
            code_key = f"lean_{target}"
            if code_key in result:
                result[code_key] = _inject_comments_into_lean(body[0], result[code_key])
            return result
        return {
            "result": False,
            "error": f"Target '{target}' only supports a single top-level statement; use --target command for full modules.",
        }

    if target == "command" and ast_json.get("node_type") in {"Comment", "DocString"}:
        return {"result": True, f"lean_{target}": _direct_comment_code(ast_json)}

    result = invoke_lean_backend(ast_json, target, client=client)
    if result.get("result") is False:
        return result
    code_key = f"lean_{target}"
    if code_key in result:
        result[code_key] = _inject_comments_into_lean(ast_json, result[code_key])
    return result
