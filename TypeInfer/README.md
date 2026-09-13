# TypeInfer — giving every Python value a Lean type

Python doesn't make you write types. Lean insists on them. This little library sits in the middle:
it works out a Lean type for each Python value, so the generated Lean code compiles instead of
getting stuck.

That's the whole job. It's a small, self-contained analysis — it depends only on Lean's JSON
library, nothing from the rest of PastaLean — so the code generator can use it freely.

## Why it's needed

When PastaLean can't tell what type a variable holds, it leaves the binder untyped and hopes Lean
figures it out:

```lean
def total := fun xs ↦ …    -- xs : what?
```

Lean can't. A top-level `def` resolves its parameter types *before* it looks at the body, so it
never works backwards from how `xs` is used. The result is an error like
`typeclass instance problem is stuck` or a number silently defaulting to the wrong type. TypeInfer's
job is to fill in that `xs : List Int` so the binder is typed and the code compiles.

## The one idea: a type lattice

Every value gets a `PyType`. Most are what you'd expect — `int`, `str`, `list[int]`,
`dict[str, int]`, `Optional[TreeNode]`. Two are special:

- **`unknown`** — "we don't know *yet*." It's the starting point for everything.
- **`any`** — "we found out it's more than one thing." A variable that's an `int` on one line and a
  `str` on another is `any`.

The key operation is **`join`**: given two things we've learned about the same value, what do we
know overall?

```
join unknown int   = int      -- learning a fact beats knowing nothing
join int int       = int      -- agreement changes nothing
join int bool      = int      -- Python's bool is a kind of int (True + 1 == 2)
join int str       = any      -- genuinely two types → give up on a single one
join (list int) (list unknown) = list int   -- containers combine element-by-element
```

`join` only ever moves *up* the lattice (`unknown → a real type → any`), never back down. That's
what lets the analysis loop over a function until nothing changes and be sure it will stop.

There's also **`consistent`**, which asks "can a value of type A be used where B is expected?" It's
what a gradual type system (Siek & Taha's work on mixing typed and untyped code) uses at the
boundary. `any` is consistent with everything, which is what will eventually let a boxed
"don't-know" value flow anywhere.

## Where the types come from

Two sources, both just reading the code:

**1. Annotations you already wrote.** `ofAnnotation` reads a Python type hint into a `PyType`:

| you wrote | TypeInfer reads |
|---|---|
| `list[int]`, `List[int]` | `list[int]` |
| `dict[str, int]` | `dict[str, int]` |
| `TreeNode | None`, `Optional[TreeNode]` | `Optional[TreeNode]` |
| `"ListNode"` (a forward reference) | `ListNode` |

**2. The shape of a literal.** `ofValue` reads the type off an expression when its shape gives it
away — no annotation needed:

| expression | TypeInfer reads |
|---|---|
| `0` | `int` |
| `2.0` | `float` |
| `"hi"` | `str` |
| `[0] * n` | `list[int]` |
| `{"a": 1}` | `dict[str, int]` |

Anything whose type isn't obvious from its shape — a bare name, a function call — comes back
`unknown`, and stays a plain untyped binder that Lean's own unifier resolves from the surrounding
body. TypeInfer only fills the gaps Lean can't.

Finally, **`toTypeSyntax?`** turns a known `PyType` into the actual Lean type text: `list[int]` →
`List Int`, `dict[str, int]` → `Std.HashMap String Int`, and so on. (`float` becomes `ℚ`, `ℝ`, or
`Float` depending on the numeric mode you asked for.)

## Examples

All of these compile and run through PastaLean today, producing the same answer as CPython.

### An annotation flows into the Lean type

```python
def total(xs: list[int]) -> int:
    s = 0
    for x in xs:
        s = s + x
    return s
```

`xs: list[int]` becomes:

```lean
def total := fun (xs : List Int) ↦ …
```

`total([1, 2, 3, 4])` prints `10`.

### A type read from a literal's shape — no annotation

```python
def running_max(nums: list[int]) -> list[int]:
    out = [0] * len(nums)      # [0] * n  →  out : list[int]
    best = nums[0]
    for i in range(len(nums)):
        if nums[i] > best:
            best = nums[i]
        out[i] = best
    return out
```

Nobody annotated `out`, but `[0] * len(nums)` is clearly a list of ints, so `out` is typed
`List Int` and the `out[i] = best` assignment type-checks. `running_max([3, 1, 4, 1, 5, 9, 2])`
prints `[3, 3, 4, 4, 5, 9, 9]`.

### A dictionary parameter

```python
def price_of(cart: dict[str, int], item: str) -> int:
    return cart.get(item, 0)
```

becomes:

```lean
def price_of := fun (cart : Std.HashMap String Int) ↦ fun (item : String) ↦ …
```

### A helper defined inside a function

PastaLean lifts a nested `def` out to its own top-level function, turning the variables it captures
into extra parameters. Those parameters need types — and that's exactly where an untyped binder used
to leave Lean stuck.

```python
def path_count(grid: list[list[int]]) -> int:
    rows = len(grid)
    cols = len(grid[0])

    def walk(r: int, c: int) -> int:
        if r >= rows or c >= cols:
            return 0
        if r == rows - 1 and c == cols - 1:
            return 1
        return walk(r + 1, c) + walk(r, c + 1)

    return walk(0, 0)
```

`walk` captures `rows` and `cols`, which become extra parameters when it's lifted out. They come
from `len(...)`, so their types are recovered by Lean's own unifier from how they're compared
against `Int`. A captured *list* — the case that used to leave Lean stuck — gets its element type
from its shape instead, exactly like `out` above. Either way the lifted helper is well-typed, and
`path_count([[0,0,0],[0,0,0]])` prints `3`.

## Following a type through a function

Reading a type off one expression isn't enough — the type learned in one line has to reach every
use. That's the fixpoint: seed each variable from what we know, then walk the function body over and
over, learning a bit more each pass, until nothing changes. Because we only ever `join` upward, it
always settles.

The payoff is the accumulator pattern, where the *literal is empty* and the type only appears later:

```python
def evens(n: int) -> list[int]:
    out = []                 # out : list[?]  — nothing to go on yet
    for i in range(n):
        out.append(i * 2)    # out.append(int) — now we know: out : list[int]
    return out
```

Nobody annotated `out`, and `[]` says nothing. But `out.append(i * 2)` teaches us the element type,
so `out` is ascribed `List Int`:

```lean
let mut out : List Int := []
```

That one ascription is what stops Lean defaulting the empty list's element to `ℚ` and getting stuck
on the later `out.append`. The same thing types a dictionary from its first `d[k] = v`, and a
lifted helper's captured variables from how the enclosing function uses them.

## Across functions

A type learned in one function is useful in another. When `total` calls `make_pairs`, it should know
what `make_pairs` hands back — even if nobody annotated its return:

```python
def make_pairs(n: int):
    result = []
    for i in range(n):
        result.append(i * i)      # result : list[int]
    return result                 # so make_pairs returns list[int]

def total() -> int:
    data = make_pairs(5)          # data : list[int], learned from make_pairs
    s = 0
    for x in data:
        s = s + x
    return s
```

Before the per-function work runs, a whole-module pass works out each function's return type — to a
fixpoint, so a function that returns another's result gets it too. Then `data = make_pairs(5)` is
ascribed `List Int`, exactly as if `make_pairs` had been annotated `-> list[int]`.

This whole-module step is a single round-trip to the Lean backend (`TypeInfer.inferModule`); the
Python side only ferries the JSON, per the rule that all analysis lives in Lean.

## What's here, and what's next

Today the library:

- reads a type from an **annotation** or a **literal's shape** (P0),
- **propagates** it through a function to a fixpoint (P1), and
- flows each function's **return type to its call sites** across the whole module (P2).

Still to come, in order:

- **Argument types to parameters** — the other half of cross-function flow: refine an unannotated
  parameter from the types it's called with.
- **`PyAny`, the total fallback** — for the slots that stay `unknown`, box the value into a single
  runtime type that holds anything. That's what makes the transpiler handle *general* Python and
  never simply fail; the cost is that a boxed value isn't provable, so it comes with a warning and a
  `--strict-types` flag to turn the warning into an error.
- **Coercions** — insert the small conversions Python does implicitly (`bool` used as an `int`,
  unwrapping an `Optional`, projecting a tuple element).

## When a value has no single type

Some Python values genuinely don't have one static type — a function that returns a string on one
branch and a number on another:

```python
def classify(x):
    if x > 0:
        return "positive"
    return 0
```

There is no Lean type that is both `String` and `Int`, so PastaLean boxes the result as `PyAny` —
a single runtime type that holds any Python value. The function compiles as returning `PyAny`, and
`classify(5)` prints `positive`, `classify(-3)` prints `0`, exactly like Python. This is the *total
fallback*: inference makes it rare, but when a value really is dynamic, boxing means the program
still compiles instead of failing. (A boxed value can't be reasoned about by the prover, so it's a
last resort.)

## Is any of this *correct*?

Because the engine is written in Lean, we don't just test it — we **prove** its core is sound, with no
`sorry`. This matters because the engine is a *monotone dataflow fixpoint over a type lattice*, and the
literature is explicit about what such an analysis must satisfy to be correct. The properties below, and
the papers that say they are the ones that matter, drive exactly which theorems we prove.

**What "correct" means for a lattice-based inferrer, and where each requirement comes from:**

| Requirement — and *why it is the right one* | Established by | Proved as (in `Theorems.lean`, on the real `PyType`) |
|---|---|---|
| The abstract domain is a **bounded join-semilattice** — so the reflow fixpoint is well-defined and its result is independent of the order/grouping in which assignments are merged | Cousot & Cousot, *Abstract Interpretation* (POPL 1977); Davey & Priestley, *Introduction to Lattices and Order* (2002) | `join_unknown_{left,right}` (⊥), `join_any_{left,right}` (⊤), `join_comm`, `join_assoc`, `join_idem` |
| **`join` is the least upper bound** of the induced precision order `a ⊑ b := a⊔b = b` — the canonical, information-minimal merge | Davey & Priestley (2002) | `le_join_left`, `le_join_right` (upper bound) + `join_le` (least); order is a partial order: `le_refl`, `le_trans`, `le_antisymm` |
| **`join` is monotone** ⇒ by Knaster–Tarski the fixpoint is a *least* fixpoint, so it exists, is unique, and terminates at bounded lattice height | Tarski, *A lattice-theoretical fixpoint theorem* (1955); Cousot & Cousot (1977) | `join_mono_left`, `join_mono_right`, `join_mono` |
| **Semantic soundness** — an inferred type never lies about the runtime: every value the program produces lies in the inferred type's denotation (the inference analogue of "well-typed programs can't go wrong") | Milner, *A Theory of Type Polymorphism* (1978); Wright & Felleisen, *A Syntactic Approach to Type Soundness* (1994) | `HasType` + `hasType_join_tower`, `hasType_join_any` (the join over-approximates) — **numeric tower proven; general containers are the open frontier** |
| **Gradual-typing consistency** for the dynamic type `PyAny` — reflexive, symmetric, and *non-transitive* (what separates gradual typing from subtyping) | Siek & Taha, *Gradual Typing for Functional Languages* (2006); Siek, Vitousek, Cimini & Boyland, *Refined Criteria for Gradual Typing* (2015) | `consistent_refl`, `consistent_symm`, `consistent_unknown`, `consistent_not_trans` |
| **`reconcile` is total** — every (expected, actual) pair maps to one of the finite intended coercions, so a value never gets "stuck" with no way to reach its slot | — | `reconcile_refl`, `reconcile_total` |

**Two honest caveats, both surfaced *by* the proofs:**

- Idempotence (`join_idem`) and order-reflexivity (`le_refl`) are stated for **`normalized`** types — those
  with no `Optional[Any]` subterm. This is not a gap but a *fact*: `join (opt any) (opt any) = any ≠ opt any`
  (`join_opt_any`), because a nullable dynamic value already *is* a dynamic value. `normalized` is exactly
  the engine's reachable normal form (it collapses `Optional[Any] → Any` by construction), so the laws hold
  everywhere the engine actually goes. The very same `Optional`/`None` absorption is what makes `join`
  **associative** at the `None`-⊔-conflict junction — `join_assoc` holds on the *full* lattice.
- Semantic soundness is proved for the numeric tower `bool <: int <: float`; extending it to a general
  denotation over every container shape is the deepest remaining piece.

**All on the production functions.** Every law — the semilattice, LUB and monotonicity laws, the
gradual-consistency laws, and `reconcile`'s totality — is proved on the **real** `PyType.join` /
`consistent` / `reconcile` the engine runs, recursing over the actual `List PyType` in `tuple`/`fn` (the
diagonal facts by well-founded recursion, the symmetric ones by each function's `.induct` principle, and
full-lattice associativity by strong induction plus `grind`). There is no stand-in model. `Theorems.lean`
is deliberately **not imported into the default build** (that associativity proof runs `grind` over every
constructor triple, which is slow); it is compiled by `lake test` (via `TestLattice.lean`) and can be
re-checked on demand with `lake build TypeInfer.Theorems`.

## Algorithm, complexity & prior art

The engine is a **monotone dataflow fixpoint over a type lattice** — the same shape as PyPy's
**RPython annotator** (reflow the whole function until nothing changes, and because `join` only ever
climbs the lattice, it provably settles). Types are recovered three ways, in a fixed precedence
(annotations > enclosing captures > call-site hints > body usage):

1. **Forward propagation** — literals, operator/builtin result types, assignment flow (Hindley–Milner
   in spirit, though monomorphic and unification-free — closer to abstract interpretation).
2. **Usage-based back-inference** — an *unannotated* parameter is pinned by how it is *used*:
   `p.split()`→str, `p << 1`→int, `ord(p)`→str, `p[k]` fixes a dict key, and **`p == <literal>` /
   `p in <literal>` pins `p` to that literal's type across every PyAny subtype** (int/bool/str/float/
   list/set/tuple). The *element* of an inferred list is recovered the same way, propagating **down
   through nested arithmetic**: `p[i] + 1`→`list[int]`, `p[i].upper()`→`list[str]`, and an int-only
   op anywhere over an element — `(p[0] + p[-1]) % 2`→`list[int]` — so `p == []` un-boxes fully, not
   just to `list[unknown]`. This is the flow-/usage-driven inference of **Shed Skin** and Agesen's
   **Cartesian Product Algorithm** (Starkiller), specialised to the shapes PastaLean emits.
3. **Gradual fallback** — a slot that stays `unknown` boxes to `PyAny`, the *Dynamic* type of **Siek &
   Taha**'s gradual typing; `consistent` (proved non-transitive in `Theorems.lean`) is its consistency
   relation.

**Complexity is deliberately linear-ish and cheap.** The reflow is capped at a small constant number
of passes (8) — sound because the lattice height is tiny, so a fixed cap is a floor, not an
approximation — giving `O(passes × body)` per function. The usage-based seed runs **once** before the
fixpoint at `O(params × body)`. There is no worklist or union-find because the lattice is shallow
enough that naive reflow already converges in ~2 passes in practice (measured: a full module infers in
tens of milliseconds). The one rule to keep it honest: usage inference must never fight a
type-*changing* reassignment (`m = "1"; m = int(m)`) — conflicting evidence `join`s up to `unknown`
(→ `PyAny`), and codegen's per-segment rebind-shadow re-types each segment, so back-inference only ever
*refines a single-typed* binding.

References: R. Milner, *A Theory of Type Polymorphism in Programming* (1978); O. Agesen, *The Cartesian
Product Algorithm* (ECOOP 1995) and M. Salib, *Starkiller: A Static Type Inferencer and Compiler for
Python* (MIT, 2004); M. Dufour, *Shed Skin: An Optimizing Python-to-C++ Compiler* (2006); the PyPy
**RPython annotator** (Rigo & Pedroni, *PyPy's Approach to Virtual Machine Construction*, 2006);
J. Palsberg & M. Schwartzbach, *Object-Oriented Type Inference* (OOPSLA 1991); and J. Siek & W. Taha,
*Gradual Typing for Functional Languages* (2006).

## The files

| file | what's in it |
|---|---|
| `PyType.lean` | the `PyType` lattice: `join`, `consistent`, `elemType` |
| `Annotation.lean` | `ofAnnotation` / `toAnnotation?` — Python type hints ↔ `PyType` |
| `Value.lean` | `ofValue` — the type of a literal, read from its shape |
| `Emit.lean` | `toTypeSyntax?` — `PyType` → Lean type text |
| `Rules.lean` | `typeOfExpr` / `applyStmt` — the type of an expression, and how a statement updates what's known |
| `Solve.lean` | `inferFunction` (the per-function fixpoint), `collectSigs` / `inferModule` (the cross-function pass), and `stampNode` (write `_ty` back onto the IR) |
| `Theorems.lean` | the proofs: the lattice laws, the partial order, monotonicity, semantic soundness, gradual-typing consistency, and `reconcile` totality — all on the real `PyType` |

The `PyAny` runtime fallback lives in `PastaLean/PyAPI/PyAny.lean`. Tests are in
`PastaLeanTest/TypeInfer/TestLattice.lean` and `TestInfer.lean` (unit checks on the lattice and the
rules) and `PastaLeanTest/PastaLeanCheck/Typing/` (worked programs).
