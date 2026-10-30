import TypeInfer.Solve.Usage
import TypeInfer.Annotation

/-!
# Exact evidence — what Python's builtin types decide outright

`usageEvidence` is an *inference* channel: its rules are hints tuned to pick a good Lean type, so the
checker has to filter them hard before accusing anything. This file is the other kind of evidence:
facts about the builtin types that hold for every value of the annotated type, so a mismatch is a
`TypeError`/`AttributeError` at run time and not a heuristic.

* An **operand** whose other side has a known type: `s + 1` with `s: str`, `x > "a"` with
  `x: float`, `n * n` with `n: str` — Python's operator tables reject these for every value.
* An **attribute** the declared builtin type does not have: `n.pop()` with `n: int`.
* A **subscript** a builtin cannot take: `xs[i]` with `i: str` and `xs` a list.
* A builtin whose argument type is fixed: `range(n)`, `chr(n)`, `ord(c)`, `sum(xs)`.

Each rule turns its fact into one requirement type `r` with the property the replay needs: `r` is
inconsistent with the declared type exactly when the operation fails for it. `.float` stands for
"some number" (the numeric tower makes `int`/`bool`/`float` all consistent with it), `.int` for "an
integer", `.str` for "a string", and a container type for "a container" — so the certificate replay
in `Certificate/Check.lean` is unchanged.

**What makes a type known here** (`exactType?`) is deliberately narrow: literals, f-strings, a
parameter whose concrete annotation is never rebound or narrowed in the body, a local bound exactly
once, the declared return of a local function, the declared type of a class field, and builtins whose
result type is fixed (`len`, `str`, `int`, …). Anything else is unknown, and unknown never accuses.
-/

namespace TypeInfer

open Lean

namespace Exact

/-! ### Builtin attribute tables (CPython 3.12, public names only) -/

def strAttrs : List String :=
  ["capitalize", "casefold", "center", "count", "encode", "endswith", "expandtabs", "find", "format",
   "format_map", "index", "isalnum", "isalpha", "isascii", "isdecimal", "isdigit", "isidentifier",
   "islower", "isnumeric", "isprintable", "isspace", "istitle", "isupper", "join", "ljust", "lower",
   "lstrip", "maketrans", "partition", "removeprefix", "removesuffix", "replace", "rfind", "rindex",
   "rjust", "rpartition", "rsplit", "rstrip", "split", "splitlines", "startswith", "strip",
   "swapcase", "title", "translate", "upper", "zfill"]

def listAttrs : List String :=
  ["append", "clear", "copy", "count", "extend", "index", "insert", "pop", "remove", "reverse", "sort"]

def dictAttrs : List String :=
  ["clear", "copy", "fromkeys", "get", "items", "keys", "pop", "popitem", "setdefault", "update",
   "values"]

def setAttrs : List String :=
  ["add", "clear", "copy", "difference", "difference_update", "discard", "intersection",
   "intersection_update", "isdisjoint", "issubset", "issuperset", "pop", "remove",
   "symmetric_difference", "symmetric_difference_update", "union", "update"]

def intAttrs : List String :=
  ["as_integer_ratio", "bit_count", "bit_length", "conjugate", "denominator", "from_bytes", "imag",
   "is_integer", "numerator", "real", "to_bytes"]

def floatAttrs : List String :=
  ["as_integer_ratio", "conjugate", "fromhex", "hex", "imag", "is_integer", "real"]

def tupleAttrs : List String := ["count", "index"]

/-- The public attributes of a builtin type, or `none` when the type is not a builtin we tabulate. -/
def attrsOf : PyType → Option (List String)
  | .str => some strAttrs
  | .int | .bool => some intAttrs
  | .float => some floatAttrs
  | .list _ => some listAttrs
  | .dict _ _ => some dictAttrs
  | .set _ => some setAttrs
  | .tuple _ => some tupleAttrs
  | _ => none

/-- `x.m` with `x: ann`: a builtin type that HAS `m` and that `ann` is inconsistent with, when `ann`
itself lacks `m`. Private and dunder names are skipped (every object has dunders), and so is a name
no builtin has — it may be a user attribute, and there is no builtin type to name as the requirement. -/
def attrEvidence (ann : PyType) (m : String) : Option PyType :=
  if m.startsWith "_" then none else
  match attrsOf ann with
  | none => none
  | some own =>
      if own.contains m then none else
      [PyType.str, .list .unknown, .dict .unknown .unknown, .set .unknown, .int, .float].find? fun t =>
        ((attrsOf t).map (·.contains m)).getD false && !PyType.consistent ann t

/-! ### Operator tables -/

def isIntLike : PyType → Bool
  | .int | .bool => true
  | _ => false

/-- The requirement an operand of `op` must meet when the OTHER operand has type `u`. `selfLeft` says
which side the judged slot is on — it matters only for `%`, where a `str` on the left is formatting
and accepts anything. `none` when the pair is legal for some value of every type we could name. -/
def operandReq (op : String) (selfLeft : Bool) (u : PyType) : Option PyType :=
  match op with
  | "add" =>
      match u with
      | .str => some .str
      | .list _ => some (.list .unknown)
      | t => if PyType.isNumeric t then some .float else none
  | "sub" | "div" | "floordiv" | "pow" => if PyType.isNumeric u then some .float else none
  | "mul" =>
      match u with
      | .str | .list _ | .tuple _ => some .int
      | .float => some .float
      | _ => none
  | "mod" => if !selfLeft && PyType.isNumeric u then some .float else none
  | "lshift" | "rshift" | "bitand" | "bitor" | "bitxor" => if isIntLike u then some .int else none
  | _ => none

/-- The requirement an operand of an ordering comparison must meet: Python 3 orders numbers with
numbers, strings with strings and lists with lists, and nothing across those. -/
def orderReq (u : PyType) : Option PyType :=
  match u with
  | .str => some .str
  | .list _ => some (.list .unknown)
  | t => if PyType.isNumeric t then some .float else none

def isOrderOp (op : String) : Bool := ["lt", "le", "gt", "ge"].contains op

/-- Result type of a builtin binary operation on two known operand types, when it is fixed. -/
def binopResult (op : String) : PyType → PyType → Option PyType
  | .str, .str => if op == "add" || op == "mod" then some .str else none
  | .str, r => if op == "mod" then some .str else if op == "mul" && isIntLike r then some .str else none
  | l, .str => if op == "mul" && isIntLike l then some .str else none
  | .list _, .list _ => if op == "add" then some (.list .unknown) else none
  | .list a, r => if op == "mul" && isIntLike r then some (.list a) else none
  | l, .list a => if op == "mul" && isIntLike l then some (.list a) else none
  | l, r =>
      if !(PyType.isNumeric l && PyType.isNumeric r) then none else
      let anyFloat := l == .float || r == .float
      match op with
      | "div" => some .float
      | "add" | "sub" | "mul" | "floordiv" | "mod" => some (if anyFloat then .float else .int)
      -- `int ** int` is a `float` for a negative exponent, so only a float operand fixes it.
      | "pow" => if anyFloat then some .float else none
      | "bitand" | "bitor" | "bitxor" =>
          if l == .bool && r == .bool then some .bool
          else if isIntLike l && isIntLike r then some .int else none
      | "lshift" | "rshift" => if isIntLike l && isIntLike r then some .int else none
      | _ => none

/-! ### Names: who binds what -/

/-- An object's fields minus the `_`-prefixed ones the pipeline stamps (`_ty`, `_line`, …). Stamps are
type annotations and positions — never a definition, binding or call — and an inferred `_ty` can be
far larger than the program it annotates, so a walk looking for program structure skips them. -/
def visible (fs : List (String × Json)) : List (String × Json) := fs.filter (fun (k, _) => !k.startsWith "_")

/-- The names a binding target binds (`x`, `a, b`, `*rest`); attribute and subscript targets bind none. -/
partial def targetNames (t : Json) : List String :=
  match nodeTypeOf t with
  | some "Name" => (nameId? t).toList
  | some "Tuple" | some "List" =>
      ((t.getObjValAs? (Array Json) "elts").toOption.getD #[]).toList.flatMap targetNames
  | some "Starred" => ((getField t "value").map targetNames).getD []
  | _ => []

/-- Every name bound anywhere under `j`, nested definitions INCLUDED — a closure's `nonlocal x` rebinds
the outer `x`, and over-approximating only makes the caller more conservative. -/
partial def boundNames (j : Json) : List String :=
  let fromField (k : String) : List String :=
    match getField j k with
    | some (.arr xs) => xs.toList.flatMap targetNames
    | some t => targetNames t
    | none => []
  let here : List String :=
    match j with
    | .obj _ =>
        fromField "target" ++ fromField "targets" ++ fromField "optional_vars" ++
        (match nodeTypeOf j with
         | some "Global" | some "Nonlocal" =>
             ((j.getObjValAs? (Array String) "names").toOption.getD #[]).toList
         | some nt =>
             if nt.startsWith "Except" || nt == "MatchAs" || nt == "MatchStar" then
               ((j.getObjValAs? String "name").toOption).toList
             else []
         | none => [])
    | _ => []
  here ++ (match j with
    | .arr xs => xs.toList.flatMap boundNames
    | .obj fs => (visible fs.toList).flatMap (fun (_, v) => boundNames v)
    | _ => [])

/-- Every parameter a `def`/`lambda` binds, in order: positional-only, positional, keyword-only, then
`*args` and `**kwargs`. -/
def allParamNames (fn : Json) : Array String :=
  let a := (getField fn "args").getD .null
  let grp (k : String) : Array String :=
    ((a.getObjValAs? (Array Json) k).toOption.getD #[]).filterMap (fun p => (p.getObjValAs? String "arg").toOption)
  let star (k : String) : Array String :=
    match getField a k with
    | some v => ((v.getObjValAs? String "arg").toOption).toArray
    | none => #[]
  grp "posonlyargs" ++ grp "args" ++ grp "kwonlyargs" ++ star "vararg" ++ star "kwarg"

/-- Is `name` (or an SSA version `name'v…` of it) among `bound`? -/
def rebinds (bound : List String) (name : String) : Bool :=
  bound.any fun b => b == name || b.startsWith (name ++ "'v")

/-- Does the body narrow `name` by runtime type (`isinstance`, `type`, `hasattr`, …) or `match` on it?
A declared type says nothing certain inside such a branch, so such a slot gets no exact evidence. -/
partial def typeTested (name : String) (j : Json) : Bool :=
  let isN (o : Option Json) : Bool := o.bind nameId? == some name
  let here : Bool :=
    match nodeTypeOf j with
    | some "Call" =>
        let fn := ((getField j "func").bind nameId?).getD ""
        let args := (j.getObjValAs? (Array Json) "args").toOption.getD #[]
        ["isinstance", "issubclass", "type", "hasattr", "getattr", "callable"].contains fn
          && isN args[0]?
    | some "Match" => isN (getField j "subject")
    | _ => false
  here || (match j with
    | .arr xs => xs.any (typeTested name)
    | .obj fs => (visible fs.toList).any (fun (_, v) => typeTested name v)
    | _ => false)

/-! ### Annotations a judgment may trust (`concreteAnnotation` takes the trusted class names) -/

def concreteHeads : List String :=
  ["int", "float", "bool", "str", "list", "List", "dict", "Dict", "set", "Set", "Optional", "None"]

/-- Is this annotation a CONCRETE type — builtin scalars, `list`/`dict`/`set`/`Optional` of concrete
types, or a class this module defines? `ofAnnotation` reads protocols (`Iterable`, `Sequence`,
`Mapping`) as the concrete container they are usually filled with, and a bare `tuple` as the empty
tuple; judging a value against those readings would accuse legal programs. -/
partial def concreteAnnotation (classes : List String) (ann : Json) : Bool :=
  match nodeTypeOf ann with
  | some "Name" =>
      let n := (nameId? ann).getD ""
      concreteHeads.contains n || classes.contains n
  | some "Constant" =>
      match getField ann "value" with
      | some .null => (ann.getObjValAs? String "python_literal_kind").toOption != some "ellipsis"
      | some (.str s) => classes.contains s
      | _ => false
  | some "Subscript" =>
      let head := ((getField ann "value").bind nameId?).getD ""
      let sl := (getField ann "slice").getD .null
      let parts : List Json := match nodeTypeOf sl with
        | some "Tuple" => ((sl.getObjValAs? (Array Json) "elts").toOption.getD #[]).toList
        | _ => [sl]
      ["list", "List", "dict", "Dict", "set", "Set", "Optional"].contains head
        && parts.all (concreteAnnotation classes)
  | _ => false

/-! ### The module a judgment is made in -/

/-- A class this module defines, as the checker needs it. -/
structure ClassInfo where
  /-- Dotted path, the scope its methods' slots are keyed under. -/
  fq : String
  bases : List String
  /-- Declared field types (`x: T` in the class body or `self.x: T = …` in a method). -/
  fields : List (String × Json)
  methods : List Json
  /-- A class decorator (`@dataclass`, `@strawberry.type`) may rewrite the class, `__init__` included. -/
  decorated : Bool := false
  deriving Inhabited

/-- Module-wide tables: classes and functions defined exactly once (a name defined twice makes every
reference to it ambiguous, so it is left out), and what can hide a builtin. -/
structure Module where
  classes : Std.HashMap String ClassInfo := {}
  /-- Bare name → (dotted path, definition). -/
  functions : Std.HashMap String (String × Json) := {}
  /-- Every name bound or imported anywhere in the module; such a name is not trusted as a builtin. -/
  hidden : Std.HashSet String := {}
  /-- A `from m import *` makes every builtin name potentially foreign. -/
  starImport : Bool := false
  /-- Imported name → `(module, member)`; `member` is `""` for `import m`. -/
  imports : Std.HashMap String (String × String) := {}
  /-- The plain local classes (`trustedClasses`), computed once. -/
  trusted : List String := []
  deriving Inhabited

partial def collectDefs (scope : String) (j : Json) : List (String × String × Json) :=
  let inScope (n : String) : String := if scope.isEmpty then n else scope ++ "." ++ n
  let nm := (j.getObjValAs? String "name").toOption.getD ""
  let here : List (String × String × Json) :=
    match nodeTypeOf j with
    | some "ClassDef" => [("class", inScope nm, j)]
    | some "FunctionDef" | some "AsyncFunctionDef" => [("fn", inScope nm, j)]
    | _ => []
  let scope' := match nodeTypeOf j with
    | some "ClassDef" | some "FunctionDef" | some "AsyncFunctionDef" => inScope nm
    | _ => scope
  let sub := match j with
    | .arr xs => xs.toList.flatMap (collectDefs scope')
    | .obj fs => (visible fs.toList).flatMap (fun (_, v) => collectDefs scope' v)
    | _ => []
  here ++ sub

/-- Each imported name with what it refers to. -/
partial def importTable (j : Json) : List (String × String × String) :=
  let here : List (String × String × String) :=
    match nodeTypeOf j with
    | some "Import" =>
        ((j.getObjValAs? (Array Json) "names").toOption.getD #[]).toList.filterMap fun a => do
          let n ← (a.getObjValAs? String "name").toOption
          let bound := ((a.getObjValAs? String "asname").toOption).getD n
          -- `import a.b` binds `a`, which is module `a`, not `a.b`.
          if (a.getObjValAs? String "asname").toOption.isNone && n.contains '.' then none
          else some (bound, n, "")
    | some "ImportFrom" =>
        let m := (j.getObjValAs? String "module").toOption.getD ""
        ((j.getObjValAs? (Array Json) "names").toOption.getD #[]).toList.filterMap fun a => do
          let n ← (a.getObjValAs? String "name").toOption
          some (((a.getObjValAs? String "asname").toOption).getD n, m, n)
    | _ => []
  here ++ (match j with
    | .arr xs => xs.toList.flatMap importTable
    | .obj fs => (visible fs.toList).flatMap (fun (_, v) => importTable v)
    | _ => [])

/-- Names an `import`/`from … import` binds. -/
partial def importedNames (j : Json) : List String :=
  let here : List String :=
    match nodeTypeOf j with
    | some "Import" | some "ImportFrom" =>
        ((j.getObjValAs? (Array Json) "names").toOption.getD #[]).toList.filterMap fun a =>
          match (a.getObjValAs? String "asname").toOption with
          | some n => some n
          | none => ((a.getObjValAs? String "name").toOption).map (fun n => (n.splitOn ".").headD n)
    | _ => []
  here ++ (match j with
    | .arr xs => xs.toList.flatMap importedNames
    | .obj fs => (visible fs.toList).flatMap (fun (_, v) => importedNames v)
    | _ => [])

/-- A star import from a module whose exports are not known. PastaLean's own contract DSL
(`contracts`/`passta`: `Requires`, `Ensures`, …) shadows no builtin. -/
partial def hasStarImport (j : Json) : Bool :=
  (nodeTypeOf j == some "ImportFrom" &&
    !["contracts", "passta"].contains ((j.getObjValAs? String "module").toOption.getD "") &&
    ((j.getObjValAs? (Array Json) "names").toOption.getD #[]).any
      (fun a => (a.getObjValAs? String "name").toOption == some "*"))
  || (match j with
      | .arr xs => xs.any hasStarImport
      | .obj fs => (visible fs.toList).any (fun (_, v) => hasStarImport v)
      | _ => false)

/-- The bare name of a dotted path. -/
def lastName (fq : String) : String := (fq.splitOn ".").getLast?.getD fq

def mkModule (ast : Json) : Module := Id.run do
  let defs := collectDefs "" ast
  let counts : Std.HashMap (String × String) Nat :=
    defs.foldl (fun m (kd, fq, _) => let k := (kd, lastName fq); m.insert k (m.getD k 0 + 1)) {}
  let count (kind n : String) : Nat := counts.getD (kind, n) 0
  -- A module-level name that is also imported or assigned may not be the definition when it is used.
  let rebound : Std.HashSet String := Std.HashSet.ofList (boundNames ast ++ importedNames ast)
  let mut m : Module := {}
  for (kind, fq, j) in defs do
    let n := lastName fq
    if fq.contains '.' || rebound.contains n then continue
    if kind == "class" && count "class" n == 1 && count "fn" n == 0 then
      let bases := ((j.getObjValAs? (Array Json) "bases").toOption.getD #[]).toList.filterMap nameId?
      let fields := ((j.getObjValAs? (Array Json) "fields").toOption.getD #[]).toList.filterMap fun f =>
        match (f.getObjValAs? String "name").toOption, getField f "decl" with
        | some fn, some ann => if ann.isNull then none else some (fn, ann)
        | _, _ => none
      let methods := ((j.getObjValAs? (Array Json) "methods").toOption.getD #[]).toList
      let decorated := !((j.getObjValAs? (Array Json) "decorator_list").toOption.getD #[]).isEmpty
      m := { m with classes := m.classes.insert n { fq, bases, fields, methods, decorated } }
    -- Only module-level definitions are reachable by a bare name from anywhere; a nested one is
    -- resolved through its enclosing body (`Ctx.localFns`).
    else if kind == "fn" && count "fn" n == 1 && count "class" n == 0 then
      m := { m with functions := m.functions.insert n (fq, j) }
  let table := importTable ast
  -- A name imported twice (or also assigned) is ambiguous.
  let imports := table.filter (fun (n, _) => (table.filter (·.1 == n)).length == 1)
  return { m with hidden := rebound, starImport := hasStarImport ast,
                  imports := Std.HashMap.ofList (imports.map (fun (n, mo, mem) => (n, (mo, mem)))) }

/-- Every base of a class, transitively — `none` when some ancestor is not defined in this module,
since a foreign base (`int`, `TypedDict`, `Protocol`, a library class) makes the class's relation to
other types unknown. -/
partial def ancestry? (m : Module) (cls : String) (fuel : Nat := 8) : Option (List String) :=
  match fuel, m.classes.get? cls with
  | 0, _ | _, none => none
  | k + 1, some ci =>
      ci.bases.foldlM (fun acc b => (ancestry? m b k).map (fun bs => acc ++ b :: bs)) []

/-- Plain local classes: undecorated, with an entirely local ancestry, none of it decorated. Only these
are trusted as annotations — a `TypedDict` accepts a dict literal and a `Protocol` any structural
match, so judging an argument against one by name would accuse legal code. -/
def trustedClasses (m : Module) : List String :=
  m.classes.toList.filterMap fun (n, ci) =>
    match ancestry? m n with
    | some anc => if ci.decorated || anc.any (fun b => (m.classes.get? b).any (·.decorated)) then none else some n
    | none => none

/-- Replace every class's fields with the ones the SOURCE declares. Inference writes each unannotated
field's inferred type into its `annotation` slot (`stampClassFields`), so on the stamped module that
slot is not a declaration; `ast` is the module before any pass ran. -/
def withDeclaredFields (m : Module) (ast : Json) : Module :=
  let raw := mkModule ast
  let m : Module := { m with classes := m.classes.fold (fun acc n ci =>
      acc.insert n { ci with fields := ((raw.classes.get? n).map (·.fields)).getD [] }) {} }
  { m with trusted := trustedClasses m }

def classNames (m : Module) : List String := m.trusted

/-- A class field's declared type, searching the class and then its bases in order. Returns the class
that declares it (its scope keys the slot) and the annotation. A base this module does not define
ends the search: it may declare the field differently. -/
partial def fieldDecl? (m : Module) (cls : String) (f : String) (fuel : Nat := 8) : Option (String × Json) :=
  match fuel, m.classes.get? cls with
  | 0, _ | _, none => none
  | k + 1, some ci =>
      match ci.fields.find? (·.1 == f) with
      | some (_, ann) => some (ci.fq, ann)
      | none => ci.bases.findSome? (fun b => fieldDecl? m b f k)

/-- The decorators on a definition: a bare name as itself, anything else (`@validate_call(...)`,
`@functools.wraps(f)`) as `"<expr>"`, so a caller asking "only staticmethod/classmethod?" sees it. -/
def decoratorNames (fn : Json) : List String :=
  ((fn.getObjValAs? (Array Json) "decorator_list").toOption.getD #[]).toList.map fun d =>
    (nameId? d).getD "<expr>"

/-- A method `meth` of `cls` or its first defining base, with the class that defines it. A method
defined twice in one class (an overload, a property setter) is ambiguous and not resolved. -/
partial def methodOf? (m : Module) (cls : String) (meth : String) (fuel : Nat := 8) : Option (String × Json) :=
  match fuel, m.classes.get? cls with
  | 0, _ | _, none => none
  | k + 1, some ci =>
      match ci.methods.filter (fun f => (f.getObjValAs? String "name").toOption == some meth) with
      | [f] => some (ci.fq, f)
      | [] => ci.bases.findSome? (fun b => methodOf? m b meth k)
      | _ => none

/-! ### Exact types -/

/-- A type made only of builtins — no class, no `Optional`. -/
partial def isBuiltinType : PyType → Bool
  | .int | .bool | .float | .str | .none => true
  | .list e | .set e => isBuiltinType e || e == .unknown
  | .dict k v => (isBuiltinType k || k == .unknown) && (isBuiltinType v || v == .unknown)
  | .tuple es => es.all (fun e => isBuiltinType e || e == .unknown)
  | _ => false

/-- Does `j` contain a best-effort `pyUnsupported(...)` placeholder? It stands for source the front end
could not translate, which may bind any name (`global x`, an assignment), so a scope holding one gets
no once-bound or uniform names and no trusted parameters. -/
partial def hasPlaceholder (j : Json) : Bool :=
  (nodeTypeOf j == some "Call" && ((getField j "func").bind nameId?) == some "pyUnsupported")
  || (match j with
      | .arr xs => xs.any hasPlaceholder
      | .obj fs => (visible fs.toList).any (fun (_, v) => hasPlaceholder v)
      | _ => false)

/-- What a judgment knows inside one function. -/
structure Ctx where
  mod : Module
  /-- Names with an exact type: trusted parameters and once-bound locals. -/
  env : Std.HashMap String PyType := {}
  /-- Every name the function binds (parameters included) — such a name is never a builtin. -/
  shadowed : Std.HashSet String := {}
  curClass : Option String := none
  /-- `self` is this function's first parameter and is never rebound, so `self.x` is the instance's. -/
  selfFree : Bool := false
  /-- Variable → the name it iterates: every value it holds is an element of that name. -/
  elemOf : Std.HashMap String String := {}
  /-- Functions defined directly in this body, by bare name → (dotted path, definition). -/
  localFns : Std.HashMap String (String × Json) := {}
  deriving Inhabited

/-- A container's shape with its contents forgotten: a once-bound local list can still be appended
to, so only its constructor is a fact. -/
def shape : PyType → PyType
  | .list _ => .list .unknown
  | .set _ => .set .unknown
  | .dict _ _ => .dict .unknown .unknown
  | t => t

def isBuiltin (c : Ctx) (f : String) : Bool :=
  !c.mod.starImport && !c.shadowed.contains f && !c.mod.hidden.contains f
    && !c.mod.functions.contains f && !c.mod.classes.contains f

/-- A declared return type, if the definition writes a concrete one. -/
def declaredReturn? (c : Ctx) (fn : Json) : Option PyType :=
  (getField fn "returns").bind fun ann =>
    if !ann.isNull && concreteAnnotation (classNames c.mod) ann then some (ofAnnotation ann) else none

/-- Method results fixed by the receiver's builtin type. -/
def methodResult : PyType → String → Option PyType
  | .str, m =>
      if ["upper", "lower", "strip", "lstrip", "rstrip", "replace", "title", "capitalize", "join",
          "format", "casefold", "swapcase", "zfill", "center", "ljust", "rjust", "removeprefix",
          "removesuffix", "expandtabs", "translate"].contains m then some .str
      else if ["find", "rfind", "index", "rindex", "count"].contains m then some .int
      else if ["startswith", "endswith", "isalpha", "isdigit", "isalnum", "isspace", "isupper",
               "islower", "isnumeric", "isdecimal", "isidentifier", "isascii", "istitle",
               "isprintable"].contains m then some .bool
      else if ["split", "rsplit", "splitlines"].contains m then some (.list .str)
      else none
  | .list _, m => if ["index", "count"].contains m then some .int else none
  | .tuple _, m => if ["index", "count"].contains m then some .int else none
  | .int, m | .bool, m => if ["bit_length", "bit_count"].contains m then some .int else none
  | _, _ => none

mutual

partial def exactType? (c : Ctx) (e : Json) : Option PyType :=
  let ty (k : String) : Option PyType := (getField e k).bind (exactType? c)
  let elts := ((e.getObjValAs? (Array Json) "elts").toOption.getD #[]).toList
  -- A literal's element type is a fact only when every element is known.
  let joined (ts : List (Option PyType)) : PyType :=
    if ts.all Option.isSome then PyType.joinAll (ts.filterMap id) else .unknown
  match nodeTypeOf e with
  | some "Constant" => match ofValue e with | .unknown => none | t => some t
  | some "JoinedStr" => some .str
  | some "List" => some (.list (joined (elts.map (exactType? c))))
  | some "Set" => some (.set (joined (elts.map (exactType? c))))
  | some "Tuple" => some (.tuple (elts.map (fun x => (exactType? c x).getD .unknown)))
  | some "Dict" => some (.dict .unknown .unknown)
  | some "ListComp" => some (.list .unknown)
  | some "SetComp" => some (.set .unknown)
  | some "DictComp" => some (.dict .unknown .unknown)
  | some "Name" => (nameId? e).bind c.env.get?
  | some "BinOp" => do
      let op ← (e.getObjValAs? String "op").toOption
      binopResult op (← ty "left") (← ty "right")
  | some "UnaryOp" => do
      let op ← (e.getObjValAs? String "op").toOption
      if op == "not" then return .bool
      let t ← ty "operand"
      match op with
      | "neg" | "pos" => if t == .float then some .float else if isIntLike t then some .int else none
      | "invert" => if isIntLike t then some .int else none
      | _ => none
  | some "Call" => callResult c e
  | some "Attribute" => do
      let v ← getField e "value"
      let f ← (e.getObjValAs? String "attr").toOption
      let cls ← (if nameId? v == some "self" && c.selfFree then c.curClass else
                   match exactType? c v with | some (.cls n) => some n | _ => none)
      let (_, ann) ← fieldDecl? c.mod cls f
      -- A class-typed field is routinely narrowed (`isinstance(self.t, Sub)`) before use, and this
      -- pass does not track narrowing through attributes; a builtin-typed one is not.
      let t := ofAnnotation ann
      if concreteAnnotation (classNames c.mod) ann && isBuiltinType t then some t else none
  | some "Subscript" => do
      let t ← ty "value"
      let isSlice := ((getField e "slice").bind nodeTypeOf) == some "Slice"
      match t with
      | .str => some .str
      | .list el => if isSlice then some (.list el) else if el == .unknown then none else some el
      | .dict _ v => if isSlice || v == .unknown then none else some v
      | _ => none
  | some "IfExp" => do
      let a ← ty "body"
      let b ← ty "orelse"
      if a == b then some a else none
  | _ => none

partial def callResult (c : Ctx) (e : Json) : Option PyType := do
  let func ← getField e "func"
  let args := (e.getObjValAs? (Array Json) "args").toOption.getD #[]
  match nodeTypeOf func with
  | some "Name" =>
      let f ← nameId? func
      if let some (_, fn) := c.localFns.get? f then declaredReturn? c fn
      else if c.shadowed.contains f then none
      else if let some (_, fn) := c.mod.functions.get? f then declaredReturn? c fn
      else if c.mod.classes.contains f then some (.cls f)
      else if !isBuiltin c f then none
      else match f with
        | "len" | "ord" | "hash" | "int" => some .int
        | "chr" | "str" | "repr" | "hex" | "bin" | "oct" | "input" | "format" => some .str
        | "float" => some .float
        | "bool" | "isinstance" | "callable" | "hasattr" => some .bool
        | "abs" => do
            let t ← args[0]? >>= exactType? c
            if t == .float then some .float else if isIntLike t then some .int else none
        | "round" => do
            let t ← args[0]? >>= exactType? c
            if args.size == 1 && PyType.isNumeric t then some .int else none
        | "sorted" | "list" => some (.list .unknown)
        | "set" => some (.set .unknown)
        | "dict" => some (.dict .unknown .unknown)
        | _ => none
  | some "Attribute" => do
      let recv ← getField func "value"
      let m ← (func.getObjValAs? String "attr").toOption
      let cls? : Option String :=
        if nameId? recv == some "self" && c.selfFree then c.curClass
        else match exactType? c recv with | some (.cls n) => some n | _ => none
      match cls? with
      | some cls => do
          let (_, fn) ← methodOf? c.mod cls m
          declaredReturn? c fn
      | none => methodResult (← exactType? c recv) m
  | _ => none

end

/-- The element type a `for` loop over a value of this type binds, when it is fixed. -/
def iterElem : PyType → Option PyType
  | .str => some .str
  | .list e | .set e => if e == .unknown then none else some e
  | .dict k _ => if k == .unknown then none else some k
  | _ => none

/-! ### The context of one function -/

/-- The trusted parameters of `fn`: concretely annotated, never rebound, never narrowed by runtime
type, with their declared types. -/
def trustedParams (m : Module) (bound : List String) (fn : Json) : List (String × PyType) :=
  let body := (getField fn "body").getD (.arr #[])
  let args := (getField fn "args").getD .null
  let group (k : String) : List Json := ((args.getObjValAs? (Array Json) k).toOption.getD #[]).toList
  (group "posonlyargs" ++ group "args" ++ group "kwonlyargs").filterMap fun a => do
    let n ← (a.getObjValAs? String "arg").toOption
    let ann ← getField a "annotation"
    if ann.isNull || n == "self" || n == "cls" then none
    else if !concreteAnnotation (classNames m) ann || rebinds bound n || typeTested n body then none
    else some (n, ofAnnotation ann)

/-- What a `for` target binds when iterating `iter`: each name with its exact type, if known, and the
name it iterates, if every value is an element of a plain name. `zip`/`enumerate` are followed
component-wise; a tuple target over a string binds one-character strings. -/
def iterBindings (c : Ctx) (target iter : Json) : List (String × Option PyType × Option String) :=
  let elemOf (e : Json) : Option PyType :=
    if nodeTypeOf e == some "Range" then some .int else (exactType? c e).bind iterElem
  match nodeTypeOf target with
  | some "Name" => (targetNames target).map (fun n => (n, elemOf iter, nameId? iter))
  | some "Tuple" | some "List" =>
      let elts := (target.getObjValAs? (Array Json) "elts").toOption.getD #[]
      let names := elts.toList.filterMap nameId?
      if names.length != elts.size then (targetNames target).map (·, none, none) else
      let fn := ((getField iter "func").bind nameId?).getD ""
      let args := (iter.getObjValAs? (Array Json) "args").toOption.getD #[]
      if nodeTypeOf iter == some "Call" && isBuiltin c fn && fn == "zip" && args.size == names.length then
        (names.zip args.toList).map fun (n, a) => (n, elemOf a, nameId? a)
      else if nodeTypeOf iter == some "Call" && isBuiltin c fn && fn == "enumerate" && args.size == 1
          && names.length == 2 then
        [(names[0]!, some .int, none), (names[1]!, elemOf args[0]!, nameId? args[0]!)]
      else if exactType? c iter == some .str then names.map (·, some .str, nameId? iter)
      else names.map (·, none, none)
  | _ => (targetNames target).map (·, none, none)

/-- Bind (or unbind) iteration targets in `c`. -/
def withBindings (c : Ctx) (bs : List (String × Option PyType × Option String)) : Ctx :=
  bs.foldl (fun c (n, t, src) =>
    { c with env := match t with | some t => c.env.insert n t | none => c.env.erase n,
             elemOf := match src with | some s => c.elemOf.insert n s | none => c.elemOf.erase n })
    c

/-- `c` inside a nested function, lambda or class body: every name that scope binds (its parameters
included) is a different variable from the outer one of that name, so it loses its outer type. -/
def enterScope (c : Ctx) (j : Json) : Ctx :=
  let own := (allParamNames j).toList ++ boundNames ((getField j "body").getD .null)
  { c with env := own.foldl (fun e n => e.erase n) c.env,
           elemOf := own.foldl (fun e n => e.erase n) c.elemOf,
           shadowed := c.shadowed.insertMany own }

/-- `c` inside a comprehension: its generators bind in order, each seeing the ones before. -/
def withGenerators (c : Ctx) (comp : Json) : Ctx :=
  ((comp.getObjValAs? (Array Json) "generators").toOption.getD #[]).foldl (fun c g =>
    withBindings c (iterBindings c ((getField g "target").getD .null) ((getField g "iter").getD .null))) c

/-- The names an expression reads. -/
partial def namesIn (j : Json) : List String :=
  (if nodeTypeOf j == some "Name" then (nameId? j).toList else []) ++
  (match j with
   | .arr xs => xs.toList.flatMap namesIn
   | .obj fs => (visible fs.toList).flatMap (fun (_, v) => namesIn v)
   | _ => [])

/-- One simple binding of a local, as `addUniform` weighs it. -/
inductive Binding where
  | assign (value : Json)
  | aug (op : String) (value : Json)
  | iter (target iter : Json)

/-- The simple bindings in a block, each with the straight-line assignments that reach it: an
earlier `v = e` in the same block (or an enclosing one) with nothing in between binding `v`, where
the binding statement itself does not bind `v` either. There `v` holds exactly `e`'s value — the
flow fact a loop target rebound in its own body (`for ch in s: ch = ord(ch)`) needs, since SSA does
not version loop-carried names. -/
partial def simpleBindings (stmts : List Json) (reach : Std.HashMap String Json) :
    List (String × Binding × Std.HashMap String Json) :=
  match stmts with
  | [] => []
  | st :: rest =>
      let live := (boundNames st).foldl (fun m v => m.erase v) reach
      let here : List (String × Binding × Std.HashMap String Json) :=
        match nodeTypeOf st, getField st "target" with
        | some "Assign", some t => match nameId? t with
            | some n => [(n, .assign ((getField st "value").getD .null), live)]
            | none => []
        | some "AugAssign", some t => match nameId? t with
            | some n => [(n, .aug ((st.getObjValAs? String "op").toOption.getD "")
                                  ((getField st "value").getD .null), live)]
            | none => []
        | some "For", some t =>
            (targetNames t).map (·, .iter t ((getField st "iter").getD .null), live)
        | _, _ => []
      let inner := (childBlocks st).flatMap (fun b => simpleBindings b live)
      let reach' := match nodeTypeOf st, (getField st "target").bind nameId?, getField st "value" with
        | some "Assign", some n, some v => live.insert n v
        | _, _, _ => live
      here ++ inner ++ simpleBindings rest reach'

/-- Extend `c` with the locals whose EVERY binding — plain assignment, augmented assignment, or plain
`for` target — has one and the same exact type. Flow-insensitive, hence sound for every program point:
if each binding writes a `T` (an augmented one computing `T` from `T`), the variable only ever holds a
`T`. `bound` is every binding the scope can see; a name with any binding not of these forms is left
out. Container contents are forgotten. -/
def addUniform (c₀ : Ctx) (bound : List String) (params : Array String) (stmts : List Json) : Ctx := Id.run do
  let simple := simpleBindings stmts {}
  let count (xs : List String) : Std.HashMap String Nat :=
    xs.foldl (fun m x => m.insert x ((m.getD x 0) + 1)) {}
  let boundCount := count bound
  -- Names with an SSA version `x'v…` somewhere: their base is rebound at another type.
  let versioned : Std.HashSet String := Std.HashSet.ofList <| bound.filterMap fun b =>
    match b.splitOn "'v" with
    | base :: _ :: _ => some base
    | _ => none
  let grouped : Std.HashMap String (List (Binding × Std.HashMap String Json)) :=
    simple.foldr (fun (n, b, r) m => m.insert n ((b, r) :: m.getD n [])) {}
  let simpleCount := grouped.fold (fun m n bs => m.insert n bs.length) ({} : Std.HashMap String Nat)
  let names := (simple.map (·.1)).eraseDups.filter fun n =>
    !params.contains n && !versioned.contains n && simpleCount.getD n 0 == boundCount.getD n 0
  -- A binding is evaluated with the straight-line assignments reaching it bound to their values —
  -- only those of names its own expression reads, so a long block is not re-typed at every binding.
  let reached (c : Ctx) (reach : Std.HashMap String Json) (e : Json) : Ctx :=
    (namesIn e).foldl (fun c' v => match reach.get? v with
      | some ve => match exactType? c ve with
          | some t => withBindings c' [(v, some (shape t), none)]
          | none => c'
      | none => c') c
  let mut c := c₀
  for _ in [0:3] do
    let before := c.env.size
    let envBefore := c.env
    for n in names do
      let bs := grouped.getD n []
      let base : List (Option PyType × Option String) := bs.filterMap fun
        | (.assign v, r) => some ((exactType? (reached c r v) v).map shape, none)
        | (.iter t it, r) => ((iterBindings (reached c r it) t it).find? (·.1 == n)).map (fun (_, ty, src) => (ty.map shape, src))
        | (.aug _ _, _) => none
      let t? : Option PyType := match base with
        | (some t, _) :: rest => if rest.all (·.1 == some t) && t != .none then some t else none
        | _ => none
      let ok := t?.any fun t => bs.all fun
        | (.aug op v, r) => ((exactType? (reached c r v) v).bind (binopResult op t)).map shape == some t
        | _ => true
      -- Only a name whose sole binding is one iteration is an element of what it iterates.
      let src : Option String := match bs, base with
        | [(.iter _ _, _)], [(_, s)] => s
        | _, _ => none
      c := if ok then withBindings c [(n, t?, src)] else withBindings c [(n, none, none)]
    if c.env.size == before && names.all (fun n => c.env.get? n == envBefore.get? n) then break
  return c

/-- The module's globals bound exactly once anywhere in the module (a `global x` in a function counts
as a binding, so such a name is never here). -/
def moduleCtx (m : Module) (ast : Json) : Ctx :=
  let stmts := (ast.getObjValAs? (Array Json) "body").toOption.getD #[]
  if hasPlaceholder ast then { mod := m } else
  addUniform { mod := m } (boundNames ast) #[] stmts.toList

/-- Build the context of one function: its trusted parameters, its once-bound locals, and the
module's once-bound globals it does not bind itself. -/
def fnCtx (m : Module) (globals : Std.HashMap String PyType) (cur : Option String) (fq : String)
    (fn : Json) : Ctx :=
  let bodyArr := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let bound := boundNames (Json.arr bodyArr)
  let params := allParamNames fn
  let shadowed : Std.HashSet String := Std.HashSet.ofList (params.toList ++ bound)
  let inherited := globals.toList.filter (fun (n, _) => !shadowed.contains n)
  -- A nested `def` is reachable by its bare name only when this body defines it once and binds the
  -- name no other way.
  let nested := (flatStmts bodyArr.toList).filter (fun st =>
    nodeTypeOf st == some "FunctionDef" || nodeTypeOf st == some "AsyncFunctionDef")
  let nestedName (st : Json) : String := (st.getObjValAs? String "name").toOption.getD ""
  let hidden := hasPlaceholder (Json.arr bodyArr)
  let localFns := nested.filterMap fun st =>
    let n := nestedName st
    if (nested.filter (nestedName · == n)).length == 1 && !shadowed.contains n
    then some (n, (fq ++ "." ++ n, st)) else none
  let c₀ : Ctx := { mod := m, curClass := cur, shadowed,
                    env := Std.HashMap.ofList (inherited ++ (if hidden then [] else trustedParams m bound fn)),
                    selfFree := !hidden && cur.isSome && params[0]? == some "self" && !rebinds bound "self",
                    localFns := Std.HashMap.ofList localFns }
  if hidden then c₀ else addUniform c₀ bound params bodyArr.toList

/-! ### Evidence about one parameter -/

/-- Does `j` introduce a new binding of `name` for its whole subtree — a nested function or lambda
taking a parameter of that name, or a comprehension iterating into it? -/
def shadowsIn (name : String) (j : Json) : Bool :=
  match nodeTypeOf j with
  | some "FunctionDef" | some "AsyncFunctionDef" | some "Lambda" => (allParamNames j).contains name
  | some "ListComp" | some "SetComp" | some "DictComp" | some "GeneratorExp" =>
      ((j.getObjValAs? (Array Json) "generators").toOption.getD #[]).any fun g =>
        ((getField g "target").map targetNames).getD [] |>.contains name
  | _ => false

/-- What a function reference names: `(module, member)` for an imported function, through
`from m import f` or `import m; m.f`. -/
def qualified? (c : Ctx) (e : Json) : Option (String × String) :=
  match nodeTypeOf e with
  | some "Name" => do
      let n ← nameId? e
      if c.shadowed.contains n then none else
      let (m, mem) ← c.mod.imports.get? n
      if mem.isEmpty then none else some (m, mem)
  | some "Attribute" => do
      let n ← (getField e "value").bind nameId?
      if c.shadowed.contains n then none else
      let (m, mem) ← c.mod.imports.get? n
      if !mem.isEmpty then none else
      some (m, ← (e.getObjValAs? String "attr").toOption)
  | _ => none

/-- The binary operator an `operator`-module function applies. -/
def operatorFn : String × String → Option String
  | ("operator", f) =>
      match f with
      | "add" => some "add" | "sub" => some "sub" | "mul" => some "mul" | "truediv" => some "div"
      | "floordiv" => some "floordiv" | "mod" => some "mod" | "pow" => some "pow"
      | "and_" => some "bitand" | "or_" => some "bitor" | "xor" => some "bitxor"
      | "lshift" => some "lshift" | "rshift" => some "rshift"
      | _ => none
  | _ => none

/-- `itertools.accumulate(name, f[, initial=v])` and `functools.reduce(f, name[, v])` with `f` an
`operator` function apply `f` to `name`'s elements — to two of them, or to `v` and the first. With
`name: str` each element is a string, so `f` must accept a string there. -/
def foldEvidence (c : Ctx) (name : String) (ann : PyType) (j : Json) : List PyType := Id.run do
  let args := (j.getObjValAs? (Array Json) "args").toOption.getD #[]
  let kw (k : String) : Option Json := match getField j "keywords" with
    | some (.obj fs) => fs.toList.lookup k
    | _ => none
  let some callee := (getField j "func").bind (qualified? c) | return []
  let (seq, f, init) : Option Json × Option Json × Option Json :=
    if callee == ("itertools", "accumulate") then (args[0]?, args[1]?, (kw "initial").orElse (fun _ => args[2]?))
    else if callee == ("functools", "reduce") then (args[1]?, args[0]?, args[2]?)
    else (none, none, none)
  if (seq.bind nameId?) != some name then return []
  if PyType.isNumeric ann then return [.list .unknown]
  if ann != .str then return []
  let some op := (f.bind (qualified? c)).bind operatorFn | return []
  let req : Option PyType := match init with
    | some v => (exactType? c v).bind (operandReq op false)
    | none => operandReq op true .str
  return match req with
    | some r => if PyType.consistent .str r then [] else [.list r]
    | none => []

/-- Every exact requirement the body places on parameter `name`, declared `ann`. -/
partial def paramEvidence (c₀ : Ctx) (name : String) (ann : PyType) (j : Json) : List PyType :=
  if shadowsIn name j then [] else
  let c := match nodeTypeOf j with
    | some "ListComp" | some "SetComp" | some "DictComp" | some "GeneratorExp" => withGenerators c₀ j
    | some "FunctionDef" | some "AsyncFunctionDef" | some "Lambda" | some "ClassDef" => enterScope c₀ j
    | _ => c₀
  let isN (o : Option Json) : Bool := o.bind nameId? == some name
  let notSlice (o : Option Json) : Bool := (o.bind nodeTypeOf) != some "Slice"
  -- `name[i]`, or a variable iterating `name`, is with `name: str` a one-character string; a
  -- requirement on it lifts to `name` as "a container of such elements", which no `str` is.
  let isElem (o : Option Json) : Bool :=
    ann == .str && o.any fun s =>
      (nodeTypeOf s == some "Subscript" && isN (getField s "value") && notSlice (getField s "slice"))
        || ((nameId? s).bind c.elemOf.get?) == some name
  let ty (o : Option Json) : Option PyType := o.bind (exactType? c)
  let lift (r : Option PyType) : List PyType :=
    match r with
    | some r => if PyType.consistent .str r then [] else [.list r]
    | none => []
  let side (selfSide other : Option Json) (req : PyType → Option PyType) : List PyType :=
    (if isN selfSide then ((ty other).bind req).toList else []) ++
    (if isElem selfSide then lift ((ty other).bind req) else [])
  let op := (j.getObjValAs? String "op").toOption.getD ""
  let here : List PyType :=
    match nodeTypeOf j with
    | some "BinOp" =>
        side (getField j "left") (getField j "right") (operandReq op true) ++
        side (getField j "right") (getField j "left") (operandReq op false)
    | some "Compare" =>
        let l := getField j "left"
        let r := getField j "right"
        if isOrderOp op then side l r orderReq ++ side r l orderReq
        else if op == "in" || op == "notin" then
          -- `x in name`: only a container holds a non-string; `name in s`: only a string is in a string.
          (if isN r then match ty l with
             | some .str | some .unknown | some .any | none => []
             | some u => [.list u]
           else []) ++
          (if isN l && ty r == some .str then [.str] else [])
        else []
    | some "Attribute" =>
        let m := (j.getObjValAs? String "attr").toOption
        if isN (getField j "value") then (m.bind (attrEvidence ann)).toList
        else if isElem (getField j "value") then lift (m.bind (attrEvidence .str))
        else []
    | some "Subscript" =>
        let v := getField j "value"
        let s := getField j "slice"
        (if isN v && ann == .str && notSlice s then
           match ty s with
           | some .int | some .bool | some .unknown | some .any | none => []
           | some u => [.dict u .unknown]
         else []) ++
        (match ty v with
         | some (.list _) | some .str | some (.tuple _) =>
             if isN s then [.int]
             else if (s.bind nodeTypeOf) == some "Slice" then
               if ["lower", "upper", "step"].any (fun k => isN (s.bind (getField · k))) then [.int] else []
             else []
         | _ => [])
    | some "Call" | some "Range" =>
        let args := (j.getObjValAs? (Array Json) "args").toOption.getD #[]
        let fn := ((getField j "func").bind nameId?).getD ""
        let builtin : List PyType :=
          if !isBuiltin c fn then [] else
          match fn with
          | "range" => if args.any (fun a => isN (some a)) then [.int] else []
          | "chr" => if isN args[0]? then [.int] else []
          | "ord" => if isN args[0]? then [.str] else []
          | "sum" => if isN args[0]? && ann == .str then [.list .float] else []
          | _ => []
        builtin ++ foldEvidence c name ann j
    | _ => []
  here ++ (match j with
    | .arr xs => xs.toList.flatMap (paramEvidence c name ann)
    | .obj fs => (visible fs.toList).flatMap (fun (_, v) => paramEvidence c name ann v)
    | _ => [])

/-- The exact types of a function's own `return e` statements (not those of nested definitions). -/
partial def returnTypes (c : Ctx) (j : Json) : List PyType :=
  match nodeTypeOf j with
  | some "FunctionDef" | some "AsyncFunctionDef" | some "Lambda" | some "ClassDef" => []
  | nt =>
      let here : List PyType :=
        if nt == some "Return" then ((getField j "value").bind (exactType? c)).toList else []
      here ++ (match j with
        | .arr xs => xs.toList.flatMap (returnTypes c)
        | .obj fs => (visible fs.toList).flatMap (fun (_, v) => returnTypes c v)
        | _ => [])

end Exact

end TypeInfer
