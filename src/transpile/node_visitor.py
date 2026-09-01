import json
import sys
import ast
from io import StringIO
from pathlib import Path
import tokenize

BINOP_MAP = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.Pow: "pow",
    ast.Div: "div",
    ast.FloorDiv: "floordiv",
    ast.BitOr: "bitor",
    ast.BitAnd: "bitand",
    ast.BitXor: "bitxor",
    ast.LShift: "lshift",
    ast.RShift: "rshift",
    ast.Mod : "mod",
}

BOOLOP_MAP = {
    ast.And: "and",
    ast.Or: "or",
}

# Container methods the backend lowers as a rebuild of their receiver. Must agree with
# `inPlaceMutatingMethods` in `PastaLean/PyGens/Core/Utils.lean`.
IN_PLACE_MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear", "sort", "reverse",
    "add", "discard", "update", "setdefault", "popitem",
    "intersection_update", "difference_update", "symmetric_difference_update",
    "appendleft", "popleft", "appendright",
})

UNARYOP_MAP = {
    ast.USub: "neg",
    ast.UAdd: "pos",
    ast.Not: "not",
    ast.Invert: "invert",   # `~x`, i.e. `-x - 1` on ints
}

COMPAREOP_MAP = {
    ast.Eq: "eq",
    ast.NotEq: "ne",
    ast.Lt: "lt",
    ast.LtE: "le",
    ast.Gt: "gt",
    ast.GtE: "ge",
    ast.In: "in",
    ast.NotIn: "notin",
    ast.Is: "is",
    ast.IsNot: "isnot",
}

AUGASSIGN_MAP = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.MatMult: "matmul",
    ast.Pow: "pow",
    ast.Mod: "mod",
    ast.LShift: "lshift",
    ast.RShift: "rshift",
    ast.BitAnd: "and",
    ast.BitOr: "or",
    ast.BitXor: "xor",
    ast.Div: "div",
    ast.FloorDiv: "floordiv",
}


"""
Use auto-serialize for nodes whose JSON form is basically:
- node_type = AST class name
- every field can just be recursively visited
- no normalization, remapping, filtering, or validation is needed
"""
AUTO_SERIALIZED_NODE_NAMES = {
    "ExceptHandler",
    "match_case",
    "alias",
}

FUNCTION_DEF_SCHEMA = {
    "node_type": "FunctionDef",
    "name": "str",
    "args": {
        "node_type": "arguments",
        "posonlyargs": ["arg"],
        "args": ["arg"],
        "vararg": "arg | None",
        "kwonlyargs": ["arg"],
        "kw_defaults": ["Json | None"],
        "kwarg": "arg | None",
        "defaults": ["Json"]
    },
    "body": ["Json"],
    "decorator_list": ["Json"],
    "returns": "Json | None",
    "type_comment": "str | None",
    "type_params": ["Json"]
}

class ASTToJsonLeanVisitorBase:
    def __init__(self, source_code="", *, best_effort=False, supported_modules=frozenset(),
                 type_only_modules=frozenset(), module_dir=None):
        self.source_code = source_code
        self.source_lines = source_code.splitlines()
        self.comment_entries = self._extract_comment_entries(source_code)
        self._next_comment_id = 0
        # Best-effort fallback: when on, statements that use a foreign (unsupported) library or
        # that fail to translate are replaced by a `pyUnsupported(...)` placeholder instead of
        # aborting the whole file. See `docs/libraries_todo.md`.
        self.best_effort = best_effort
        self.supported_modules = frozenset(supported_modules)
        self.type_only_modules = frozenset(type_only_modules)
        self.module_dir = module_dir
        self.foreign_names = set()      # locally-bound names that come from foreign modules
        self.unsupported_log = []       # original source of every dropped/degraded statement
        self._next_unsup_id = 0         # for naming top-level placeholder defs

    def _is_foreign_module(self, module_name):
        """A module is foreign if it is neither a supported library, a type-only module, nor a
        local sibling `.py` we could translate ourselves."""
        if not isinstance(module_name, str) or not module_name:
            return False
        root = module_name.split(".")[0]
        if root in self.supported_modules or root in self.type_only_modules:
            return False
        if self.module_dir and (Path(self.module_dir) / f"{root}.py").exists():
            return False
        return True

    def _import_is_foreign(self, stmt):
        """True for an `import`/`from ... import` of a foreign module."""
        if isinstance(stmt, ast.Import):
            return any(self._is_foreign_module(a.name) for a in stmt.names)
        if isinstance(stmt, ast.ImportFrom):
            return self._is_foreign_module(stmt.module)
        return False

    def _compute_foreign_names(self, module_node):
        """Names bound by foreign imports anywhere in the module (so their later use can be
        recognised and replaced)."""
        names = set()
        for node in ast.walk(module_node):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if self._is_foreign_module(alias.name):
                        # `import a.b.c` binds `a`; `import a.b as x` binds `x`.
                        names.add(alias.asname or alias.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                if self._is_foreign_module(node.module):
                    for alias in node.names:
                        names.add(alias.asname or alias.name)
        # Propagate: a value derived from a foreign one is itself foreign
        # (`logger = logging.getLogger()` makes `logger` foreign), to a fixpoint.
        assigns = [n for n in ast.walk(module_node) if isinstance(n, (ast.Assign, ast.AnnAssign))]
        changed = True
        while changed:
            changed = False
            for node in assigns:
                if node.value is None:
                    continue
                if not any(isinstance(n, ast.Name) and n.id in names for n in ast.walk(node.value)):
                    continue
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for tgt in targets:
                    for nm in ast.walk(tgt):
                        if isinstance(nm, ast.Name) and nm.id not in names:
                            names.add(nm.id)
                            changed = True
        return names

    def _stmt_uses_foreign(self, stmt):
        """True if the statement references any foreign-imported name."""
        if not self.foreign_names:
            return False
        for node in ast.walk(stmt):
            if isinstance(node, ast.Name) and node.id in self.foreign_names:
                return True
        return False

    def _unsupported_call(self, func_name, source_text):
        return {
            "node_type": "Call",
            "func": {"node_type": "Name", "id": func_name},
            "args": [{"node_type": "Constant", "value": source_text}],
            "keywords": {},
        }

    def _assign_target_json(self, stmt):
        """If `stmt` is an assignment to a plain Name (or tuple of Names), return its target IR
        so the placeholder can keep the variable declared; otherwise None."""
        target = None
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            target = stmt.targets[0]
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            target = stmt.target
        if isinstance(target, ast.Name):
            return {"node_type": "Name", "id": target.id}
        if isinstance(target, (ast.Tuple, ast.List)) and all(
            isinstance(e, ast.Name) for e in target.elts
        ):
            return {"node_type": "Tuple", "elts": [{"node_type": "Name", "id": e.id} for e in target.elts]}
        return None

    def _make_unsupported_node(self, stmt, top_level=False):
        """Rewrite an unsupported statement into a `pyUnsupported("<source>")` placeholder,
        reusing the ordinary Assign/Expr codegen paths. The single concrete-typed sink keeps any
        assigned variable *declared* (no unconstrained `Inhabited ?m`). A bare statement becomes
        `let _ := pyUnsupported ...`; at top level it is kept as a synthetic `def __py_unsup_N`
        rather than removed."""
        src = ast.get_source_segment(self.source_code, stmt) or "<unsupported>"
        src = " ".join(src.split())  # collapse to one line for a clean Lean string literal
        self.unsupported_log.append(src)

        target_json = self._assign_target_json(stmt)
        if target_json is not None:
            return {"node_type": "Assign", "target": target_json,
                    "value": self._unsupported_call("pyUnsupported", src)}

        if top_level:
            # Don't drop a top-level bare statement — keep it as a named placeholder def.
            name = f"__py_unsup_{self._next_unsup_id}"
            self._next_unsup_id += 1
            return {"node_type": "Assign",
                    "target": {"node_type": "Name", "id": name},
                    "value": self._unsupported_call("pyUnsupported", src)}
        return {"node_type": "Expr", "value": self._unsupported_call("pyUnsupported", src)}

    # Statements whose sub-bodies are themselves translated through `visit_body_statements`; we
    # must NOT degrade these wholesale on foreign use, or a single foreign line would swallow a
    # whole function/loop. They recurse so their inner statements degrade individually.
    _SCOPE_OR_BODY_STMTS = tuple(
        getattr(ast, name) for name in (
            "FunctionDef", "AsyncFunctionDef", "ClassDef", "If", "For", "AsyncFor",
            "While", "Try", "With", "AsyncWith", "Match",
        ) if hasattr(ast, name)
    )

    def _translate_body_stmt(self, stmt, top_level=False):
        """Translate one statement, applying the best-effort fallback when enabled. Returns the
        IR node, or None to drop the statement (foreign imports)."""
        if not self.best_effort:
            return self.visit(stmt)
        if self._import_is_foreign(stmt):
            return None  # foreign import contributes nothing; drop it
        if not isinstance(stmt, self._SCOPE_OR_BODY_STMTS) and self._stmt_uses_foreign(stmt):
            return self._make_unsupported_node(stmt, top_level=top_level)
        try:
            return self.visit(stmt)
        except NotImplementedError:
            return self._make_unsupported_node(stmt, top_level=top_level)

    def _new_comment_id(self):
        comment_id = str(self._next_comment_id)
        self._next_comment_id += 1
        return comment_id

    def _comment_block_lines(self, source_code):
        """Ignore PALC directive blocks so harness comments do not leak into generated Lean."""
        ignored = set()
        in_block = False
        for line_no, raw_line in enumerate(source_code.splitlines(), start=1):
            stripped = raw_line.strip()
            if stripped == "# PastaLeanCHECK START":
                in_block = True
            if in_block:
                ignored.add(line_no)
            if stripped == "# PastaLeanCHECK END":
                in_block = False
        return ignored

    def _extract_comment_entries(self, source_code):
        """Collect standalone source comments with line/indent information for later body interleaving."""
        if not source_code:
            return []
        ignored_lines = self._comment_block_lines(source_code)
        entries = []
        for tok in tokenize.generate_tokens(StringIO(source_code).readline):
            if tok.type != tokenize.COMMENT:
                continue
            line_no, col = tok.start
            if line_no in ignored_lines:
                continue
            raw_line = self.source_lines[line_no - 1] if 0 <= line_no - 1 < len(self.source_lines) else ""
            if not raw_line.lstrip().startswith("#"):
                continue
            text = tok.string[1:].lstrip()
            entries.append({"line": line_no, "indent": col, "text": text})
        return entries

    def _body_comments_between(self, start_line, end_line, indent):
        """Return standalone comments that belong to one lexical block gap."""
        if start_line > end_line:
            return []
        result = []
        for entry in self.comment_entries:
            if start_line <= entry["line"] <= end_line and entry["indent"] == indent:
                result.append({
                    "node_type": "Comment",
                    "comment_id": self._new_comment_id(),
                    "text": entry["text"],
                })
        return result

    def _is_docstring_stmt(self, stmt):
        return (
            isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and isinstance(stmt.value.value, str)
        )

    def _make_docstring_node(self, text):
        return {
            "node_type": "DocString",
            "comment_id": self._new_comment_id(),
            "text": text,
        }

    def visit_body_statements(self, statements, *, body_start_line=1, body_end_line=None, allow_docstring=False, top_level=False):
        """Translate a statement list while interleaving standalone comments and leading docstrings."""
        if body_end_line is None:
            body_end_line = len(self.source_lines)
        if not statements:
            return []

        body_indent = getattr(statements[0], "col_offset", 0)
        result = []
        cursor_line = body_start_line
        start_idx = 0

        if allow_docstring and self._is_docstring_stmt(statements[0]):
            doc_stmt = statements[0]
            result.extend(self._body_comments_between(cursor_line, doc_stmt.lineno - 1, body_indent))
            result.append(self._make_docstring_node(doc_stmt.value.value))
            cursor_line = getattr(doc_stmt, "end_lineno", doc_stmt.lineno) + 1
            start_idx = 1

        for stmt in statements[start_idx:]:
            stmt_line = getattr(stmt, "lineno", cursor_line)
            result.extend(self._body_comments_between(cursor_line, stmt_line - 1, body_indent))
            if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
                cursor_line = getattr(stmt, "end_lineno", stmt_line) + 1
                continue
            # A bare string-literal statement is a no-op wherever it sits — including a docstring
            # displaced below a `Requires(...)`, which `allow_docstring` above cannot see.
            if self._is_docstring_stmt(stmt):
                result.append(self._make_docstring_node(stmt.value.value))
                cursor_line = getattr(stmt, "end_lineno", stmt_line) + 1
                continue
            translated = self._translate_body_stmt(stmt, top_level=top_level)
            if translated is not None:
                result.append(translated)
            cursor_line = getattr(stmt, "end_lineno", stmt_line) + 1

        result.extend(self._body_comments_between(cursor_line, body_end_line, body_indent))
        return result

    def _map_ast_type(self, node_or_type, mapping, label):
        """Map an AST node type through a shared lookup table."""
        node_type = type(node_or_type) if isinstance(node_or_type, ast.AST) else node_or_type
        mapped = mapping.get(node_type)
        if mapped is None:
            raise NotImplementedError(f"{label} {node_type.__name__} not supported.")
        return mapped

    def _serialize_node_fields(self, node):
        """Serialize an AST node by visiting all of its fields recursively."""
        result: dict[str, object] = {"node_type": type(node).__name__}
        for field_name, value in ast.iter_fields(node):
            result[field_name] = self._serialize_field_value(value)
        return result

    def _serialize_field_value(self, value):
        """Recursively serialize one AST field value."""
        if isinstance(value, ast.AST):
            return self.visit(value)
        if isinstance(value, list):
            return [self._serialize_field_value(item) for item in value]
        return value

    def _visit_match_node(self, node):
        """Generic serializer for Python structural pattern-matching AST nodes."""
        return self._serialize_node_fields(node)

    def _visit_auto_serialized_node(self, node):
        """Generic serializer for explicitly whitelisted AST nodes."""
        return self._serialize_node_fields(node)

    def visit_statements(self, statements):
        """Translate a statement list, skipping declaration-only annotations."""
        return self.visit_body_statements(statements)

    def visit(self, node):
        """
        The dynamic dispatcher. Routes an AST node to its specific visit_X method.
        """
        # Base case: raw primitives
        if not isinstance(node, ast.AST):
            return node
            
        # Determine the name of the method we need
        method_name = f"visit_{type(node).__name__}"
        
        # Fetch the specific method, falling back to generic_visit if it doesn't exist
        visitor = getattr(self, method_name, None)
        if visitor is None and (
            type(node).__name__.startswith("Match") or type(node).__name__ == "match_case"
        ):
            visitor = self._visit_match_node
        if visitor is None and type(node).__name__ in AUTO_SERIALIZED_NODE_NAMES:
            visitor = self._visit_auto_serialized_node
        if visitor is None:
            visitor = self.generic_visit
        # print(f"Visiting node type: {type(node).__name__} with visitor method: {visitor.__name__}", file=sys.stderr)  # Debugging output
        
        return visitor(node)

    def generic_visit(self, node):
        """Strict fallback to prevent unsupported syntax from leaking into the IR."""
        raise NotImplementedError(f"Translation for {type(node).__name__} is not supported in the current subset.")
    

    def visit_BinOp(self, node):
        """Translates ast.BinOp (e.g., a + b) to a JSON IR node."""
        left_json = self.visit(node.left)
        right_json = self.visit(node.right)
        op = self._map_ast_type(node.op, BINOP_MAP, "Operator")
            
        return {
            "node_type": "BinOp",
            "op": op,
            "left": left_json,
            "right": right_json
        }
    
    def visit_BoolOp(self, node):
        """Translates ast.BoolOp (e.g., a and b) to a JSON IR node."""
        op = self._map_ast_type(node.op, BOOLOP_MAP, "Boolean operator")
        
        return {
            "node_type": "BoolOp",
            "op": op,
            "values": [self.visit(value) for value in node.values]
        }

    def visit_UnaryOp(self, node):
        """Translates ast.UnaryOp (e.g., -a) to a JSON IR node."""
        op = self._map_ast_type(node.op, UNARYOP_MAP, "Unary operator")
        
        return {
            "node_type": "UnaryOp",
            "op": op,
            "operand": self.visit(node.operand)
        }

    def _single_compare(self, left_json, op_ast, right_json):
        """Build one Compare IR node from already-visited operands."""
        return {
            "node_type": "Compare",
            "op": self._map_ast_type(op_ast, COMPAREOP_MAP, "Comparison operator"),
            "left": left_json,
            "right": right_json,
        }

    def visit_Compare(self, node):
        """Translates ast.Compare (e.g., a <= b) to a JSON IR node.

        Chained comparisons like `a < b < c` are expanded to `(a < b) and (b < c)`, the
        same desugaring Python uses (each middle operand is evaluated once at the IR level
        here; side-effecting middle operands are out of scope)."""
        operands = [self.visit(node.left)] + [self.visit(c) for c in node.comparators]
        comparisons = [
            self._single_compare(operands[i], node.ops[i], operands[i + 1])
            for i in range(len(node.ops))
        ]
        if len(comparisons) == 1:
            return comparisons[0]
        return {
            "node_type": "BoolOp",
            "op": "and",
            "values": comparisons,
        }
    
    def visit_Constant(self, node):
        """Translates ast.Constant (e.g., 42, "hello") to a JSON IR node."""
        result = {
            "node_type": "Constant",
            "value": node.value
        }
        if isinstance(node.value, float):
            result["python_literal_kind"] = "float"
            # Preserve how the float was written: a source `1e5` keeps the scientific
            # `Float.ofScientific` form; a plain decimal becomes a readable `(0.25 : Float)`.
            segment = ast.get_source_segment(self.source_code, node) or ""
            if "e" in segment or "E" in segment:
                result["float_notation"] = "scientific"
        return result
        
    def visit_NamedExpr(self, node):
        """Translates the walrus `x := e`. The Lean desugar pass hoists it into an assignment."""
        return {
            "node_type": "NamedExpr",
            "target": self.visit(node.target),
            "value": self.visit(node.value),
        }

    def visit_Nonlocal(self, node):
        """Translates `nonlocal a, b`. Closure conversion threads these names through the helper."""
        return {"node_type": "Nonlocal", "names": list(node.names)}

    def visit_Expr(self, node):
        """Translates ast.Expr (e.g., a standalone expression) to a JSON IR node."""
        return {
            "node_type": "Expr",
            "value": self.visit(node.value)
        }

    def visit_Pass(self, node):
        """Translates ast.Pass to a JSON IR no-op node."""
        return {
            "node_type": "Pass"
        }

    def visit_Break(self, node):
        """Translates ast.Break to a JSON IR node."""
        return {
            "node_type": "Break"
        }

    def visit_Continue(self, node):
        """Translates ast.Continue to a JSON IR node."""
        return {
            "node_type": "Continue"
        }
    
    def visit_Name(self, node):
        """Translates ast.Name (e.g., variable names) to a JSON IR node."""
        return {
            "node_type": "Name",
            "id": node.id
        }
    def visit_Call(self, node):
        """Translates ast.Call (e.g., function calls) to a JSON IR node."""
        func_json = self.visit(node.func)
        args_json = [self.visit(arg) for arg in node.args]
        keywords_json = {kw.arg: self.visit(kw.value) for kw in node.keywords}
        if func_json.get("node_type") == "Name" and func_json.get("id") == "range":
            return {
                "node_type": "Range",
                "func": func_json,
                "args": args_json,
                "keywords": keywords_json
            }
        # `min(a, b, ...)` / `max(a, b, ...)` (two or more positional args) is the
        # element-wise form. Normalize it to the single-iterable form `min([a, b, ...])`
        # so the backend's iterable-based `pyMin`/`pyMax` handles both call shapes.
        if (
            func_json.get("node_type") == "Name"
            and func_json.get("id") in {"min", "max"}
            and len(args_json) >= 2
            and not keywords_json
        ):
            args_json = [{"node_type": "List", "elts": args_json}]
        # `set()` with no arguments is the empty set; lower it to an empty set literal so the
        # backend needs no zero-argument `set` builtin (`set(xs)` stays a call to `pySet`).
        if (
            func_json.get("node_type") == "Name"
            and func_json.get("id") == "set"
            and not args_json
            and not keywords_json
        ):
            return {"node_type": "Set", "elts": []}
        # `list()` / `tuple()` with no arguments is the empty list; `list(x)`/`tuple(x)` stay
        # calls (lowered to `pyList`).
        if (
            func_json.get("node_type") == "Name"
            and func_json.get("id") in {"list", "tuple"}
            and not args_json
            and not keywords_json
        ):
            return {"node_type": "List", "elts": []}
        # `dict()` with no arguments is the empty dict.
        if (
            func_json.get("node_type") == "Name"
            and func_json.get("id") == "dict"
            and not args_json
            and not keywords_json
        ):
            return {"node_type": "Dict", "entries": []}
        return {
            "node_type": "Call",
            "func": func_json,
            "args": args_json,
            "keywords": keywords_json
        }
    
    def visit_Attribute(self, node):
        """Translates ast.Attribute (e.g., object.attribute) to a JSON IR node."""
        value_json = self.visit(node.value)
        attribute = node.attr
        return {
            "node_type": "Attribute",
            "value": value_json,
            "attr": node.attr,
            
        }

    def visit_Subscript(self, node):
        """Translates ast.Subscript (e.g., list[int]) to a JSON IR node."""
        return {
            "node_type": "Subscript",
            "value": self.visit(node.value),
            "slice": self.visit(node.slice)
        }

    def visit_Slice(self, node):
        """Translates ast.Slice (e.g., [start:stop:step]) to a JSON IR node."""
        return {
            "node_type": "Slice",
            "lower": self.visit(node.lower) if node.lower is not None else None,
            "upper": self.visit(node.upper) if node.upper is not None else None,
            "step": self.visit(node.step) if node.step is not None else None
        }

    def visit_List(self, node):
        """Translates ast.List to a JSON IR node."""
        return {
            "node_type": "List",
            "elts": [self.visit(elt) for elt in node.elts]
        }

    def visit_Dict(self, node):
        """Translates ast.Dict to a JSON IR node."""
        entries = []
        for key, value in zip(node.keys, node.values):
            if key is None:
                # `{**d}` spread: `value` is the dict being merged in (no key).
                entries.append({"spread": self.visit(value)})
            else:
                entries.append({
                    "key": self.visit(key),
                    "value": self.visit(value),
                })
        return {
            "node_type": "Dict",
            "entries": entries
        }

    def visit_Starred(self, node):
        """Translates ast.Starred (`*iterable`) used as a call argument."""
        return {
            "node_type": "Starred",
            "value": self.visit(node.value)
        }

    def visit_Set(self, node):
        """Translates ast.Set (`{a, b, c}` set literal) to a JSON IR node."""
        return {
            "node_type": "Set",
            "elts": [self.visit(elt) for elt in node.elts]
        }

    def visit_Tuple(self, node):
        """Translates ast.Tuple (e.g., tuple slices) to a JSON IR node."""
        return {
            "node_type": "Tuple",
            "elts": [self.visit(elt) for elt in node.elts]
        }

    def visit_JoinedStr(self, node):
        """Translates f-strings to a JSON IR node."""
        return {
            "node_type": "JoinedStr",
            "values": [self.visit(value) for value in node.values]
        }

    def visit_FormattedValue(self, node):
        """Translates one interpolated f-string segment."""
        if node.conversion != -1:
            raise NotImplementedError("FormattedValue conversions are not supported.")
        result = {
            "node_type": "FormattedValue",
            "value": self.visit(node.value),
        }
        if node.format_spec is not None:
            spec = self._const_format_spec(node.format_spec)
            if spec is None:
                raise NotImplementedError("Only constant f-string format specs are supported.")
            result["format_spec"] = spec
        return result

    @staticmethod
    def _const_format_spec(fmt):
        """A format spec is itself a (usually constant) JoinedStr, e.g. `.2f`. Extract the literal
        text if it is a single constant string; otherwise None (dynamic specs unsupported)."""
        if isinstance(fmt, ast.Constant) and isinstance(fmt.value, str):
            return fmt.value
        if (isinstance(fmt, ast.JoinedStr) and len(fmt.values) == 1
                and isinstance(fmt.values[0], ast.Constant)
                and isinstance(fmt.values[0].value, str)):
            return fmt.values[0].value
        return None

    def visit_Module(self, node):
        """Translates ast.Module to a JSON IR node."""
        if self.best_effort:
            self.foreign_names = self._compute_foreign_names(node)
        return {
            "node_type": "Module",
            "body": self.visit_body_statements(
                node.body,
                body_start_line=1,
                body_end_line=len(self.source_lines),
                allow_docstring=True,
                top_level=True,
            )
        }

    def visit_Delete(self, node):
        """Translates ast.Delete (e.g., del x) to a JSON IR node."""
        return {
            "node_type": "Delete",
            "targets": [self.visit(target) for target in node.targets]
        }


    def visit_Import(self, node):
        """Translate `import ...` statements into a lightweight IR node.

        Each alias is tagged `foreign` (see `_is_foreign_module`), so the Lean header emitter can
        skip it: `import random` has no Lean module, while `import helper` (a sibling `.py`) does.
        """
        names = []
        for alias in node.names:
            alias_json = self.visit(alias)
            if isinstance(alias_json, dict):
                alias_json["foreign"] = self._is_foreign_module(alias.name)
            names.append(alias_json)
        return {
            "node_type": "Import",
            "names": names,
        }

    def visit_ImportFrom(self, node):
        """Translate `from ... import ...` statements into a lightweight IR node."""
        return {
            "node_type": "ImportFrom",
            "module": node.module,
            "names": [self.visit(alias) for alias in node.names],
            "level": node.level,
            "foreign": self._is_foreign_module(node.module),
        }

    def visit_FunctionDef(self, node):
        """Translates ast.FunctionDef to a JSON IR node."""
        body_json = self.visit_body_statements(
            node.body,
            body_start_line=getattr(node, "lineno", 1) + 1,
            body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            allow_docstring=True,
        )
        return {
            "node_type": "FunctionDef",
            "name": node.name,
            "args": self.visit(node.args),
            "body": body_json,
            "decorator_list": [self.visit(decorator) for decorator in node.decorator_list],
            "returns": self.visit(node.returns) if node.returns is not None else None,
            "type_comment": node.type_comment,
            "type_params": [self.visit(type_param) for type_param in getattr(node, "type_params", [])]
        }
    def _self_attr_name(self, target):
        """If `target` is the AST for `self.X`, return the attribute name `X`, else None."""
        if (isinstance(target, ast.Attribute)
                and isinstance(target.value, ast.Name)
                and target.value.id == "self"):
            return target.attr
        return None

    def _self_rooted_attr(self, target):
        """The field name of the `self.X` at the root of an access path, peeling `[...]`/`.attr`
        links: `self.c[x]`, `self.g[i][j]` and `self.a.b` all reach into `self.c`/`self.g`/`self.a`.
        Under value semantics writing through such a path rebuilds `self`."""
        node = target
        while isinstance(node, (ast.Subscript, ast.Attribute)):
            name = self._self_attr_name(node)
            if name is not None:
                return name
            node = node.value
        return None

    def _add_class_field(self, fields, seen, name, annotation, default, init=None):
        """Record a class field, merging type/default info if the name is already known.

        First occurrence fixes order; a later annotated/defaulted occurrence upgrades a
        previously-unknown annotation or default. `annotation`/`default`/`init` are raw AST nodes
        (or None) and get visited to IR here. `init` is what the constructor assigns to the field
        (`self.c = [0] * n`); the backend reads its type off that when there is no annotation.
        """
        ann_json = self.visit(annotation) if annotation is not None else None
        def_json = self.visit(default) if default is not None else None
        init_json = self.visit(init) if init is not None else None
        if name in seen:
            idx = seen[name]
            if ann_json is not None and fields[idx]["annotation"] is None:
                fields[idx]["annotation"] = ann_json
            if def_json is not None and fields[idx]["default"] is None:
                fields[idx]["default"] = def_json
            if init_json is not None and fields[idx]["init"] is None:
                fields[idx]["init"] = init_json
        else:
            seen[name] = len(fields)
            fields.append({"name": name, "annotation": ann_json, "default": def_json,
                           "init": init_json})

    def _collect_self_fields(self, body, fields, seen, param_types=None):
        """Harvest `self.X` assignment targets from a method body into the field list.

        Descends into nested compound-statement blocks (if/for/while/with/try) so
        conditionally-set attributes still become fields, but never descends into nested
        function/class scopes. `param_types` maps a parameter name to its annotation AST so the
        common `self.x = x` constructor pattern picks up the field type from the parameter.
        """
        param_types = param_types or {}
        for stmt in body:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            if isinstance(stmt, ast.AnnAssign):
                name = self._self_attr_name(stmt.target)
                if name is not None:
                    self._add_class_field(fields, seen, name, stmt.annotation, None)
            elif isinstance(stmt, ast.Assign):
                for tgt in stmt.targets:
                    name = self._self_attr_name(tgt)
                    if name is not None:
                        # `self.x = x` where `x` is a typed parameter -> use the param's type.
                        # Otherwise pass the RHS along; the backend infers the type from it.
                        ann = None
                        if (isinstance(stmt.value, ast.Name)
                                and stmt.value.id in param_types):
                            ann = param_types[stmt.value.id]
                        self._add_class_field(fields, seen, name, ann, None, init=stmt.value)
            elif isinstance(stmt, ast.AugAssign):
                name = self._self_attr_name(stmt.target)
                if name is not None:
                    self._add_class_field(fields, seen, name, None, None)
            for block_attr in ("body", "orelse", "finalbody"):
                block = getattr(stmt, block_attr, None)
                if isinstance(block, list):
                    self._collect_self_fields(block, fields, seen, param_types)
            for handler in getattr(stmt, "handlers", []):
                self._collect_self_fields(handler.body, fields, seen, param_types)

    def _mutates_self_in_place(self, stmt):
        """True for `self.X.append(v)` / `self.X[i].add(v)` … — an in-place container method on a
        `self`-rooted receiver, which value semantics lower to a rebuild of `self`."""
        call = stmt.value if isinstance(stmt, ast.Expr) else stmt
        return (isinstance(call, ast.Call)
                and isinstance(call.func, ast.Attribute)
                and call.func.attr in IN_PLACE_MUTATING_METHODS
                and self._self_rooted_attr(call.func.value) is not None)

    def _method_mutates_self(self, funcdef):
        """True iff any statement in the method (excluding nested scopes) writes through self.X."""
        def walk(body):
            for stmt in body:
                if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    continue
                if isinstance(stmt, ast.AnnAssign) and self._self_rooted_attr(stmt.target):
                    return True
                if isinstance(stmt, ast.Assign) and any(
                    self._self_rooted_attr(t) for t in stmt.targets
                ):
                    return True
                if isinstance(stmt, ast.AugAssign) and self._self_rooted_attr(stmt.target):
                    return True
                if self._mutates_self_in_place(stmt):
                    return True
                for block_attr in ("body", "orelse", "finalbody"):
                    block = getattr(stmt, block_attr, None)
                    if isinstance(block, list) and walk(block):
                        return True
                for handler in getattr(stmt, "handlers", []):
                    if walk(handler.body):
                        return True
            return False
        return walk(funcdef.body)

    def visit_ClassDef(self, node):
        """Translates ast.ClassDef to a JSON IR node (Python class -> Lean structure + namespace).

        Fields are harvested from the *raw* AST (`self.X = ...` and class-level `x = ...`),
        because `visit_AnnAssign` collapses `x: T = v` to a plain `Assign` and would otherwise
        drop the field type. Methods are reused as ordinary `FunctionDef` IR nodes; the backend
        re-typed them with an explicit `self` and namespaces them under the class name.
        """
        if node.keywords:
            raise NotImplementedError("Class keyword arguments (e.g. metaclass=) are not supported.")
        if len(node.bases) > 1:
            raise NotImplementedError("Multiple inheritance is not supported.")
        bases = []
        for base in node.bases:
            if isinstance(base, ast.Name):
                if base.id != "object":
                    bases.append(self.visit(base))
            else:
                raise NotImplementedError("Only a single simple (Name) base class is supported.")

        fields = []
        seen = {}
        methods = []
        mutators = []
        staticmethods = []
        classmethods = []

        # A leading class docstring is captured here (the per-statement loop below skips bare
        # `ast.Expr` strings); the backend renders it as the structure's `/-- … -/` doc comment.
        docstring = None
        if node.body and self._is_docstring_stmt(node.body[0]):
            docstring = node.body[0].value.value

        for stmt in node.body:
            if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                self._add_class_field(fields, seen, stmt.target.id, stmt.annotation, stmt.value)
            elif (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                  and isinstance(stmt.targets[0], ast.Name)):
                self._add_class_field(fields, seen, stmt.targets[0].id, None, stmt.value)
            elif isinstance(stmt, ast.FunctionDef):
                methods.append(self.visit(stmt))
                deco_names = {d.id for d in stmt.decorator_list if isinstance(d, ast.Name)}
                is_static = "staticmethod" in deco_names
                if is_static:
                    staticmethods.append(stmt.name)
                if "classmethod" in deco_names:
                    classmethods.append(stmt.name)
                if not is_static:
                    if self._method_mutates_self(stmt):
                        mutators.append(stmt.name)
                    param_types = {
                        a.arg: a.annotation
                        for a in stmt.args.args
                        if a.annotation is not None
                    }
                    self._collect_self_fields(stmt.body, fields, seen, param_types)
            elif isinstance(stmt, (ast.Pass, ast.Expr)):
                continue  # docstring or `pass`
            else:
                raise NotImplementedError(
                    f"Unsupported statement in class body: {type(stmt).__name__}"
                )

        return {
            "node_type": "ClassDef",
            "name": node.name,
            "bases": bases,
            "decorator_list": [self.visit(d) for d in node.decorator_list],
            "docstring": docstring,
            "fields": fields,
            "methods": methods,
            "mutators": mutators,
            "staticmethods": staticmethods,
            "classmethods": classmethods,
        }

    def visit_Lambda(self, node):
        """Translates ast.Lambda to a JSON IR node."""
        return {
            "node_type": "Lambda",
            "args": self.visit(node.args),
            "body": self.visit(node.body)
        }
    
    def visit_arguments(self, node):
        """Translates ast.arguments to a JSON IR node."""
        return {
            "node_type": "arguments",
            "posonlyargs": [self.visit(arg) for arg in node.posonlyargs],
            "args": [self.visit(arg) for arg in node.args],
            "vararg": self.visit(node.vararg) if node.vararg is not None else None,
            "kwonlyargs": [self.visit(arg) for arg in node.kwonlyargs],
            "kw_defaults": [
                self.visit(default) if default is not None else None
                for default in node.kw_defaults
            ],
            "kwarg": self.visit(node.kwarg) if node.kwarg is not None else None,
            "defaults": [self.visit(default) for default in node.defaults]
        }

    def visit_arg(self, node):
        """Translates ast.arg to a JSON IR node."""
        return {
            "node_type": "arg",
            "arg": node.arg,
            "annotation": self.visit(node.annotation) if node.annotation is not None else None,
            "type_comment": node.type_comment
        }

    def visit_Assign(self, node):
        """Translates ast.Assign to a JSON IR node. A single target keeps the `target` field; a
        chained assignment (`a = b = v`, multiple targets) is emitted faithfully as a `targets`
        list and split into sequential assignments by the Lean desugar pass."""
        if len(node.targets) == 1:
            return {
                "node_type": "Assign",
                "target": self.visit(node.targets[0]),
                "value": self.visit(node.value),
            }
        return {
            "node_type": "Assign",
            "targets": [self.visit(t) for t in node.targets],
            "value": self.visit(node.value),
        }
    
    def visit_AnnAssign(self, node):
        """Translates ast.AnnAssign (e.g., x: int = 42) to a JSON IR node.

        We normalize the common initialized form `x: T = v` to the same IR node as
        `x = v`, because the current Lean backend does not yet use Python-side type
        annotations during code generation. We keep declaration-only annotated
        assignments (`x: T`) distinct so the backend can decide how to handle them.
        """
        # An *initialized* annotated assignment `target: T = v` collapses to a plain `Assign`
        # regardless of target shape — including attribute targets like `self.x: int = v`, which
        # `annotate_python` introduces inside class methods (these are non-`simple`). Field types
        # are recovered separately from the raw AST in `visit_ClassDef`.
        if node.value is not None:
            return {
                "node_type": "Assign",
                "target": self.visit(node.target),
                "value": self.visit(node.value)
            }
        if node.simple != 1:
            raise NotImplementedError("Only simple declaration-only annotations are supported.")
        return {
            "node_type": "AnnAssign",
            "target": self.visit(node.target),
            "annotation": self.visit(node.annotation),
            "value": None
        }

    def visit_AugAssign(self, node):
        """Translates ast.AugAssign (e.g., x += y) to a JSON IR node."""
        op = self._map_ast_type(node.op, AUGASSIGN_MAP, "Augmented operator")
        return {
            "node_type": "AugAssign",
            "target": self.visit(node.target),
            "op": op,
            "value": self.visit(node.value)
        }

    def visit_For(self, node):
        """Translates ast.For to a JSON IR node."""
        return {
            "node_type": "For",
            "target": self.visit(node.target),
            "iter": self.visit(node.iter),
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
            "orelse": self.visit_body_statements(
                node.orelse,
                body_start_line=(getattr(node.body[-1], "end_lineno", getattr(node, "lineno", 1)) + 1) if node.body else getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            )
        }

    def visit_If(self, node):
        """Translates ast.If to a JSON IR node."""
        return {
            "node_type": "If",
            "test": self.visit(node.test),
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
            "orelse": self.visit_body_statements(
                node.orelse,
                body_start_line=(getattr(node.body[-1], "end_lineno", getattr(node, "lineno", 1)) + 1) if node.body else getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            )
        }

    def visit_IfExp(self, node):
        """Translates ast.IfExp (ternary expressions) to a JSON IR node."""
        return {
            "node_type": "IfExp",
            "test": self.visit(node.test),
            "body": self.visit(node.body),
            "orelse": self.visit(node.orelse)
        }

    def visit_With(self, node):
        """Translates ast.With to a JSON IR node."""
        return {
            "node_type": "With",
            "items": [self.visit(item) for item in node.items],
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            )
        }
        
    def visit_withitem(self, node):
        """Translates ast.withitem (the context manager part of with statements) to a JSON IR node."""
        return {
            "node_type": "withitem",
            "context_expr": self.visit(node.context_expr),
            "optional_vars": self.visit(node.optional_vars) if node.optional_vars is not None else None
        }

    def visit_While(self, node):
        """Translates ast.While to a JSON IR node."""
        return {
            "node_type": "While",
            "test": self.visit(node.test),
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
            "orelse": self.visit_body_statements(
                node.orelse,
                body_start_line=(getattr(node.body[-1], "end_lineno", getattr(node, "lineno", 1)) + 1) if node.body else getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            )
        }

    def visit_IfExp(self, node):
        """Translates ast.IfExp (ternary expressions) to a JSON IR node."""
        return {
            "node_type": "IfExp",
            "test": self.visit(node.test),
            "body": self.visit(node.body),
            "orelse": self.visit(node.orelse)
        }

    def visit_Return(self, node):
        """Translates ast.Return to a JSON IR node."""
        return {
            "node_type": "Return",
            "value": None if node.value is None else self.visit(node.value)
        }

    def visit_Try(self, node):
        """Translates ast.Try (Exception handling) to a JSON IR node."""
        last_body_end = None
        if node.body:
            last_body_end = getattr(
                node.body[-1],
                "end_lineno",
                getattr(node.body[-1], "lineno", getattr(node, "lineno", 1)),
            )
        last_orelse_end = None
        if node.orelse:
            last_orelse_end = getattr(
                node.orelse[-1],
                "end_lineno",
                getattr(node.orelse[-1], "lineno", getattr(node, "lineno", 1)),
            )
        if last_orelse_end is not None:
            finalbody_start = last_orelse_end + 1
        elif last_body_end is not None:
            finalbody_start = last_body_end + 1
        else:
            finalbody_start = getattr(node, "lineno", 1) + 1
        return {
            "node_type": "Try",
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
            "handlers": [self.visit(handler) for handler in node.handlers],
            "orelse": self.visit_body_statements(
                node.orelse,
                body_start_line=(getattr(node.body[-1], "end_lineno", getattr(node, "lineno", 1)) + 1) if node.body else getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
            "finalbody": self.visit_body_statements(
                node.finalbody,
                body_start_line=finalbody_start,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            )
        }

    def visit_ExceptHandler(self, node):
        """Translates ast.ExceptHandler with comment-aware body handling."""
        return {
            "node_type": "ExceptHandler",
            "type": self.visit(node.type) if node.type is not None else None,
            "name": node.name,
            "body": self.visit_body_statements(
                node.body,
                body_start_line=getattr(node, "lineno", 1) + 1,
                body_end_line=getattr(node, "end_lineno", len(self.source_lines)),
            ),
        }

    def visit_match_case(self, node):
        """Translates ast.match_case with comment-aware body handling."""
        first_stmt_line = getattr(node.body[0], "lineno", 1) if node.body else 1
        last_stmt_end = getattr(node.body[-1], "end_lineno", first_stmt_line) if node.body else first_stmt_line
        return {
            "node_type": "match_case",
            "pattern": self.visit(node.pattern),
            "guard": None if node.guard is None else self.visit(node.guard),
            "body": self.visit_body_statements(
                node.body,
                body_start_line=first_stmt_line,
                body_end_line=last_stmt_end,
            ),
        }

    def visit_Raise(self, node):
        """Translates ast.Raise to a JSON IR node."""
        return {
            "node_type": "Raise",
            "exc": None if node.exc is None else self.visit(node.exc),
            "cause": None if node.cause is None else self.visit(node.cause),
        }
    
    def visit_ListComp(self, node):
        """Translates ast.ListComp (list comprehensions) to a JSON IR node."""
        return {
            "node_type": "ListComp",
            "elt": self.visit(node.elt),
            "generators": [self.visit(gen) for gen in node.generators]
        }

    def visit_GeneratorExp(self, node):
        """Translates ast.GeneratorExp using the same IR shape as comprehensions."""
        return {
            "node_type": "GeneratorExp",
            "elt": self.visit(node.elt),
            "generators": [self.visit(gen) for gen in node.generators]
        }

    def visit_SetComp(self, node):
        """Translates ast.SetComp (set comprehensions) — same IR shape as a list comprehension;
        the backend lowers the produced list and deduplicates it into the set runtime."""
        return {
            "node_type": "SetComp",
            "elt": self.visit(node.elt),
            "generators": [self.visit(gen) for gen in node.generators]
        }

    def visit_DictComp(self, node):
        """Translates ast.DictComp (dict comprehensions). Like a comprehension but with a
        key/value pair per element; the backend builds a hash map from the produced pairs."""
        return {
            "node_type": "DictComp",
            "key": self.visit(node.key),
            "value": self.visit(node.value),
            "generators": [self.visit(gen) for gen in node.generators]
        }
    
    def visit_comprehension(self, node):
        """Translates ast.comprehension (the generator part of comprehensions) to a JSON IR node."""
        return {
            "node_type": "comprehension",
            "target": self.visit(node.target),
            "iter": self.visit(node.iter),
            "ifs": [self.visit(if_cond) for if_cond in node.ifs],
            "is_async": node.is_async
        }

        
    def visit_Assert(self, node):
        """Translates ast.Assert to a JSON IR node."""
        return {
            "node_type": "Assert",
            "test": self.visit(node.test),
            "msg": None if node.msg is None else self.visit(node.msg),
        }


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python node_visitor.py <python_file.py>")
        sys.exit(1)

    input_file = sys.argv[1]
    with open(input_file, "r") as f:
        source_code = f.read()

    # Parse the source code into an AST
    tree = ast.parse(source_code)
    print(ast.dump(tree, indent = 4))  # Debugging output to verify AST structure
    visitor = ASTToJsonLeanVisitorBase()
    json_ir = visitor.visit(tree)

    print(json.dumps(json_ir, indent=2))
