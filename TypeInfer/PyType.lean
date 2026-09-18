import Lean

/-!
# The type lattice

`PyType` is what PastaLean knows about a Python value. It is a lattice with two special elements:

* `unknown` (⊥) — nothing known *yet*. Joining it with anything yields that thing.
* `any` (⊤) — conflicting information. `int` on one path and `str` on another joins to `any`,
  which is the signal to box the value as `PyAny`.

`join` is the least upper bound: start every slot at `unknown` and join in what the program says
about it until nothing changes. This is the classic reflow-to-fixpoint of PyPy's RPython annotator
and Shed Skin.
-/

namespace TypeInfer

/-- Inductive type for representing all supported Python Types in PastaLean -/
inductive PyType where
  /-- Nothing known yet — the lattice bottom. -/
  | unknown
  /-- Conflicting types — the lattice top. Boxed as `PyAny`. -/
  | any
  | int
  | bool
  | str
  /-- Python `float`. Lowers to `ℚ`, `ℝ` or `Float` depending on the numeric mode. -/
  | float
  /-- The type of `None`. -/
  | none
  | list  (elem : PyType)
  | set   (elem : PyType)
  | tuple (elems : List PyType)
  | dict  (key val : PyType)
  /-- `Optional[T]` — `T` or `None`. -/
  | opt   (inner : PyType)
  /-- A user class, `TreeNode`, `ListNode`, … -/
  | cls   (name : String)
  /-- A function type — `Callable[[A, B], R]`. The type of a decorator's wrapped parameter, and of
  a function passed as a value. -/
  | fn    (args : List PyType) (ret : PyType)
  deriving Inhabited, Repr

namespace PyType

@[simp, grind]
def beq : PyType → PyType → Bool
  | .unknown, .unknown | .any, .any | .int, .int | .bool, .bool
  | .str, .str | .float, .float | .none, .none => true
  | .list a, .list b | .set a, .set b | .opt a, .opt b => beq a b
  | .dict k₁ v₁, .dict k₂ v₂ => beq k₁ k₂ && beq v₁ v₂
  | .cls a, .cls b => a == b
  | .tuple as, .tuple bs =>
      as.length == bs.length && (as.zip bs).attach.all fun ⟨(a, b), _⟩ => beq a b
  | .fn as r₁, .fn bs r₂ =>
      as.length == bs.length && ((as.zip bs).attach.all fun ⟨(a, b), _⟩ => beq a b) && beq r₁ r₂
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        obtain ⟨ha, hb⟩ := List.of_mem_zip h
        have := List.sizeOf_lt_of_mem ha
        have := List.sizeOf_lt_of_mem hb
        omega

instance : BEq PyType := ⟨beq⟩

def toString : PyType → String
  | .unknown => "?"
  | .any => "Any"
  | .int => "int"
  | .bool => "bool"
  | .str => "str"
  | .float => "float"
  | .none => "None"
  | .list e => s!"list[{toString e}]"
  | .set e => s!"set[{toString e}]"
  | .dict k v => s!"dict[{toString k}, {toString v}]"
  | .opt i => s!"Optional[{toString i}]"
  | .cls n => n
  | .tuple es => "tuple[" ++ String.intercalate ", " (es.map toString) ++ "]"
  | .fn as r => "Callable[[" ++ String.intercalate ", " (as.map toString) ++ s!"], {toString r}]"

instance : ToString PyType := ⟨toString⟩

/-- The class a field access projects from. An `Option`-wrapped node still projects its class's
fields (`root.left` where `root : Optional[TreeNode]`) — codegen inserts the unwrap. -/
def classNameOf? : PyType → Option String
  | .cls n => Option.some n
  | .opt (.cls n) => Option.some n
  | _ => Option.none

/-- True when the type is fully determined, so a Lean type can be emitted for it. -/
def isKnown : PyType → Bool
  | .unknown | .any => false
  | .list e | .set e | .opt e => isKnown e
  | .dict k v => isKnown k && isKnown v
  | .tuple es => es.attach.all fun ⟨e, _⟩ => isKnown e
  | .fn as r => (as.attach.all fun ⟨e, _⟩ => isKnown e) && isKnown r
  | _ => true
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        have := List.sizeOf_lt_of_mem h
        omega

/-- A mutable container that lowers to a `Ref` under `--heap` (list/dict/set). A tuple is an
immutable value type, so it is excluded — matching the driver's `_CONTAINER_ANN_HEADS`. -/
def isContainer : PyType → Bool
  | .list _ | .set _ | .dict _ _ => true
  | _ => false

/-- Should a *local* binding of this type be ascribed at all? Only discrete scalars, where an
unascribed literal would otherwise default (`5` → `ℚ` in exact mode). Containers/floats are left for
Lean to infer from the assignment RHS, so an ascription never *forces* an element type (e.g. `ℚ`)
against what the RHS actually elaborates to (e.g. a numpy `Float`). Parameters are ascribed
separately — this governs only locals. -/
def needsAscription : PyType → Bool
  | .int | .bool | .str => true
  -- A container of concrete scalars (`list[int]`, `set[str]`, `list[list[int]]`) is unambiguous, so
  -- ascribing it is safe *and* needed: without it a `List Int` local can be silently unified up to
  -- `List ℚ` by a cross-variable link (`vk = stk.pop()` with `vk` a float), which then fails when the
  -- element is read as an `Int`. `float`/`unknown` elements stay unascribed (the numpy-`Float` hazard).
  | .list e | .set e => needsAscription e
  -- Same reasoning for a dict of concrete scalars (`graph = {}` refined to `dict[int, int]`): it is
  -- unambiguous, and without the ascription a captured dict is lifted as an untyped parameter and
  -- `PyGetItem ?m …` goes stuck. A `float`/`unknown` side stays unascribed, as above.
  | .dict k v => needsAscription k && needsAscription v
  -- A tuple of concrete scalars is unambiguous too (`t = []; t.append((i, j))` → `list[(int,int)]`),
  -- and without it a captured list-of-pairs is lifted untyped.
  | .tuple es => !es.isEmpty && es.attach.all fun ⟨e, _⟩ => needsAscription e
  -- The known-dynamic top type materialises as `PyAny`, which Lean cannot infer from a heterogeneous
  -- literal's first element — so a container wrapping it (`list[any]` → `List PyAny`) must be ascribed.
  | .any => true
  -- A nullable local always needs its ascription: initialised from `None`, `let mut x := Option.none`
  -- fixes the slot to `Option ?α` — a stuck metavariable a later `x = (l, r)` / `x = curr.next` cannot
  -- back-pin. Ascribe `Option τ` for any fully-known inner `τ` (node class, pair, scalar, container).
  | .opt e => isKnown e
  -- A function type must be ascribed whenever it is fully known: a heap `list` of closures builds up
  -- from an empty `allocM []`, which leaves the element's (function) domain universe stuck unless the
  -- local's type pins it — `list[Callable[[], str]]` → `List (Unit → String)`.
  | .fn as r => as.all isKnown && isKnown r
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        have := List.sizeOf_lt_of_mem h
        omega

/-- Does this type contain a function type anywhere? A container of closures cannot have its element
(function-domain) universe inferred from an empty `allocM []` literal, so under `--heap` its binding
must be ascribed even though a plain empty container is normally left for Lean to infer. -/
def containsFn : PyType → Bool
  | .fn _ _ => true
  | .list e | .set e | .opt e => containsFn e
  | .dict k v => containsFn k || containsFn v
  | .tuple es => es.attach.any fun ⟨e, _⟩ => containsFn e
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        have := List.sizeOf_lt_of_mem h
        omega

/-- Least upper bound.

`unknown` carries no information, so it yields to anything. Genuinely incompatible types (`int` and
`str`) go to `any`. `bool` joins into `int` because Python's `bool` is a subclass of `int`
(`True + 1 = 2`), and `None` joins into `Optional`.
-/
@[simp, grind]
def join : PyType → PyType → PyType
  | .unknown, t | t, .unknown => t
  | .any, _ | _, .any => .any
  -- Python's numeric tower `bool <: int <: float`: the join widens rather than becoming a union, so
  -- e.g. a `[float('inf')]*n` list also written with ints stays `list[float]` (not `list[Any]`), and
  -- the int values coerce (`Int → ℚ`) instead of failing container resolution.
  | .int, .bool | .bool, .int => .int
  | .float, .int | .int, .float | .float, .bool | .bool, .float => .float
  | .none, .none => .none
  -- `opt` before `none`, or `None ⊔ Optional[int]` would nest to `Optional[Optional[int]]`.
  -- ABSORPTION: `Optional[Any]` collapses to `Any` (a nullable dynamic value is just a dynamic value).
  -- Without it `join` is non-associative — `join(join(None,int),str) = opt any` but
  -- `join(None, join(int,str)) = any` (the `_, .any => any` rung above fires first) — which makes the
  -- fixpoint non-confluent (`Option PyAny` on one order, `PyAny` on another) for None+conflict slots.
  | .opt a, .opt b => match join a b with | .any => .any | j => .opt j
  | .opt a, .none | .none, .opt a => .opt a
  | .opt a, b | b, .opt a => match join a b with | .any => .any | j => .opt j
  | .none, t | t, .none => .opt t
  | .list a, .list b => .list (join a b)
  | .set a, .set b => .set (join a b)
  | .dict k₁ v₁, .dict k₂ v₂ => .dict (join k₁ k₂) (join v₁ v₂)
  | .tuple as, .tuple bs =>
      if as.length == bs.length then .tuple ((as.zip bs).attach.map fun ⟨(a, b), _⟩ => join a b)
      else .any
  | .fn as r₁, .fn bs r₂ =>
      if as.length == bs.length then .fn ((as.zip bs).attach.map fun ⟨(a, b), _⟩ => join a b) (join r₁ r₂)
      else .any
  | a, b => if a.beq b then a else .any
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        obtain ⟨ha, hb⟩ := List.of_mem_zip h
        have := List.sizeOf_lt_of_mem ha
        have := List.sizeOf_lt_of_mem hb
        omega

/-- Join a whole list, starting from `unknown`. -/
def joinAll (ts : List PyType) : PyType := ts.foldl join .unknown

/-- Greatest lower bound — the dual of `join`, with `any` (⊤) the identity and `unknown` (⊥) absorbing.

`join` merges values that FLOW INTO a slot, so it widens (`int` and `float` assigned to the same
variable make it `float`). `meet` merges the REQUIREMENTS a slot's uses impose, so it narrows: a
parameter used both as an `int` and as a `float` must be `int`, since an `int` satisfies both uses but
a `float` does not. Requirements that cannot be met together bottom out at `unknown`, which is the
signal a checker reports rather than boxes. -/
def meet : PyType → PyType → PyType
  | .any, t | t, .any => t
  | .unknown, _ | _, .unknown => .unknown
  -- Dual of `join`'s numeric tower `bool <: int <: float`: the meet narrows DOWN the tower.
  | .int, .bool | .bool, .int => .bool
  | .float, .int | .int, .float => .int
  | .float, .bool | .bool, .float => .bool
  -- `opt` rungs before the container ones, mirroring `join`. `Optional[T] ⊓ None = None` (the only
  -- value both admit); `Optional[T] ⊓ U` drops the nullability, since `U` alone admits no `None`.
  | .opt a, .opt b => .opt (meet a b)
  | .opt _, .none | .none, .opt _ => .none
  | .opt a, b | b, .opt a => meet a b
  | .list a, .list b => .list (meet a b)
  | .set a, .set b => .set (meet a b)
  | .dict k₁ v₁, .dict k₂ v₂ => .dict (meet k₁ k₂) (meet v₁ v₂)
  | .tuple as, .tuple bs =>
      if as.length == bs.length then .tuple ((as.zip bs).attach.map fun ⟨(a, b), _⟩ => meet a b)
      else .unknown
  | .fn as r₁, .fn bs r₂ =>
      if as.length == bs.length then .fn ((as.zip bs).attach.map fun ⟨(a, b), _⟩ => meet a b) (meet r₁ r₂)
      else .unknown
  | a, b => if a.beq b then a else .unknown
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        obtain ⟨ha, hb⟩ := List.of_mem_zip h
        have := List.sizeOf_lt_of_mem ha
        have := List.sizeOf_lt_of_mem hb
        omega

/-- Meet a whole list of requirements, starting from `any` (⊤, "no requirement yet"). -/
def meetAll (ts : List PyType) : PyType := ts.foldl meet .any

/-- Gradual-typing *consistency* (Siek & Taha): reflexive and symmetric, **not** transitive.
`any` is consistent with everything, so a boxed value may flow anywhere; `int` and `str` are not
consistent with each other. -/
def consistent : PyType → PyType → Bool
  | .any, _ | _, .any | .unknown, _ | _, .unknown => true
  -- Python's numeric tower `bool <: int <: float` — consistent so `join` (which widens to `float`)
  -- stays consistent with each operand.
  | .int, .bool | .bool, .int => true
  | .float, .int | .int, .float | .float, .bool | .bool, .float => true
  | .list a, .list b | .set a, .set b | .opt a, .opt b => consistent a b
  | .opt a, b | b, .opt a => b.beq .none || consistent a b
  | .dict k₁ v₁, .dict k₂ v₂ => consistent k₁ k₂ && consistent v₁ v₂
  | .tuple as, .tuple bs =>
      as.length == bs.length && (as.zip bs).attach.all fun ⟨(a, b), _⟩ => consistent a b
  | .fn as r₁, .fn bs r₂ =>
      as.length == bs.length && ((as.zip bs).attach.all fun ⟨(a, b), _⟩ => consistent a b) && consistent r₁ r₂
  | a, b => a.beq b
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        obtain ⟨ha, hb⟩ := List.of_mem_zip h
        have := List.sizeOf_lt_of_mem ha
        have := List.sizeOf_lt_of_mem hb
        omega

/-- Is this a number Python arithmetic accepts? -/
def isNumeric : PyType → Bool
  | .int | .bool | .float => true
  | _ => false

/-- The element type an iterable yields, or `unknown`. Strings iterate as one-character strings. -/
def elemType : PyType → PyType
  | .list e | .set e => e
  | .str => .str
  | .dict k _ => k
  | .tuple es => joinAll es
  -- Indexing/iterating a boxed value yields a boxed value.
  | .any => .any
  | _ => .unknown

/-- For a builtin that iterates its single argument (`min`/`max`/`sum` over one container), the
result type: the element type of a KNOWN container — even when still `unknown`, so a transiently
under-determined element doesn't leak the container type back onto the target — or the argument
itself when it is a scalar (`min(x)` on an un-inferred `x`). -/
def containerElemOrSelf : PyType → PyType
  | .list e | .set e => e
  | .str => .str
  | .dict k _ => k
  | .tuple es => joinAll es
  | .any => .any
  | other => other

/-- What to do when a value of type `actual` reaches a position expecting `expected`: the small
implicit coercion Python performs, or `box` (fall back to `PyAny`) when the types are unrelated. -/
inductive Reconcile where
  /-- Types already agree — no coercion. -/
  | exact
  /-- `actual` is `bool`, `expected` is `int` — `True` is `1` (`pyBoolToInt`). -/
  | boolToInt
  /-- `actual` is an integer, `expected` is `float` — widen `Int → Rat`. -/
  | intToFloat
  /-- `actual` is `Optional[T]`, `expected` is `T` — unwrap the `Option`. -/
  | unwrapOpt
  /-- Unrelated types — box both as `PyAny`. -/
  | box
  deriving Repr, BEq, DecidableEq

namespace Reconcile end Reconcile

/-- Decide the coercion from `actual` to `expected`. The wired-up cases today are `boolToInt`
(runtime instances), tuple projection (codegen) and `box` (`PyAny`); `intToFloat`/`unwrapOpt`
name the remaining ones. -/
def reconcile (expected actual : PyType) : Reconcile :=
  if expected.beq actual then .exact
  else match expected, actual with
    | .int, .bool => .boolToInt
    | .float, .int | .float, .bool => .intToFloat
    | t, .opt u => if t.beq u then .unwrapOpt else .box
    | e, a => if consistent e a then .exact else .box

end PyType
end TypeInfer
