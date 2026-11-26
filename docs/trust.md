# What a PastaLean proof is a proof of

PastaLean emits every Python function `f` twice. The provable twin `f` uses exact numbers (ℚ, ℝ),
`List`, and pure monads (`Id`, `PyExceptId`, the `PyProofM` state model of IO), and turns `assert`s
into proof obligations. The runnable twin `f'rn` uses `Float`, `Array`, and `IO`, and drops the
asserts. Theorems are proved about `f`. The program that runs is `f'rn`. So the trust argument
has three links:

```
CPython  ≈ (tested)  f'rn  ⊒ (proved, per program)  f  ⊢ (proved)  the contract
```

1. **CPython ≈ `f'rn`.** This link is tested, not proved: the runnable twin is run against CPython
   on the datasets' own tests and on stdin programs (`pastalean run`, `run_differential`, the
   cp_harness), and `pastalean refute` replays the witnesses it finds in CPython.
2. **`f'rn` ⊒ `f`.** This link is proved per program by translation validation. For each pair the
   checker states and proves, inside Lean,

   ```lean
   theorem f._twin    : ∀ a₁ … aₙ, f'rn (up a₁) … (up aₙ) = up (f a₁ … aₙ)
   theorem f._twin_eq : ∀ b₁ … bₙ, f'rn b₁ … bₙ = up (f (down b₁) … (down bₙ))   -- @[twin]
   ```

   Here `up`/`down` is the twin relation (below), which is the identity wherever the two binder types
   agree. When every type agrees, the statement is just `f'rn = f`.
3. **`f` ⊢ contract.** These are the user's theorems, checked by Lean's kernel.

The earlier wording, that the twins are "identical", is false as stated. Fewer than half of the
pairs in the reviewed examples are textually identical once the `'rn` suffix is removed. What we
claim and check is the refinement in link 2, and the table below lists every difference we treat as
legitimate.

## The twin relation

`PastaLean/PyVerify/Twin.lean` defines

```lean
class TwinRel (β : Type) (α : outParam Type) where   -- β runnable, α provable
  up : α → β
  down : β → α
  down_up : ∀ a, down (up a) = a
  up_down : ∀ b, up (down b) = b
```

`up` is the embedding of the provable world into the runnable one (the `TwinEmb.emb` of the original
plan). It is a bijection because a loop whose state holds an `Array` is checked by *conjugating* it
into the loop over the `List` state, and that needs both directions. The instances are: identity
(low priority), `Array β ↔ List α`, `List β ↔ List α` (elementwise), `Prod`, `MProd` (the tuples of a
`do` loop's mutable variables), `Option`, and `Except ε`. For a user class `C`, the checker generates
a field-wise `TwinRel C'rn C` together with constructor and projection rewrite lemmas.

There is deliberately **no `Float ↔ ℚ` instance**. IEEE rounding makes that link a refinement up to
an error enclosure, not an equation (see the table).

## How a pair is checked

`#twin_check` (`PastaLean/PyVerify/Twin/Check.lean`) pairs each declaration `X'rn` of the file with
`X`. The pairing strips `'rn` from every name component, so `C'rn.m ↦ C.m` and `main''rn ↦ main'`,
and it matches `private` and non-private twins of a memoised helper. Pairs are visited callee-first.
For each pair the checker:

- builds the statement from the two types. If no `TwinRel` exists between the binder or result
  types, the pair is classified (`float`, `monad`, `io_main`, `class`, `type`) and not attempted;
- runs `twin_tac`: `intros`, then `simp only [f, f'rn, twin]`, then `rfl`. The `@[twin]` simp set
  rewrites the runnable program into the provable one:
  - **Array runtime ↦ List runtime**: `pyArrayAppend l.toArray v = (pyAppend l v).toArray`, and the
    same for each `pyArray*` op and each `Array` protocol instance (`pyGetItem`, `pySetItem`,
    `pyModifyItem`, `pyLen`, `pySlice`, `pyContains`, `pyTruthy`, `PyBool`, `PyPrintable`,
    `pyClear`, `pyCount`, `pyIndex`, `pyIter`, iteration). Lists of runnable elements (the rows of
    a 2-D DP table) are `l.map up` in normal form and have conjugated lemmas;
  - **Bool tests ↦ decided Props**: `a == b`, `a != b`, `&&`, `||`, `!` become `decide` of the
    `=`, `≠`, `∧`, `∨`, `¬` that the provable twin branches on, so the two `if`s match even though
    their `Decidable` instances were built differently;
  - **loops**: `forIn_twin` / `forIn'_twin` rewrite a `for` loop whose state type holds runnable
    data into `up <$>` the loop over the canonical state. They fire only on a `TwinNontriv` state,
    so each loop is rewritten once;
  - **callees**: every proved `g._twin_eq` is in the set, so `g'rn` inside `f'rn` becomes
    `up ∘ g ∘ down`;
  - plumbing: `panic! = default`, `up`/`down` through constructors, projections, `ite`/`dite`, and
    the monad laws needed to push `up <$>` inward.
- adds `f._twin` (kernel-checked) and the derived `f._twin_eq`, so callers can use it.

**`partial def`s** are opaque constants in Lean's logic, so no equation about `f'rn` itself is
provable. For these the checker proves the strongest statement that is available,
**step equivalence**: the defining functionals, read from `f._unsafe_rec` / `f'rn._unsafe_rec` with
the recursive call abstracted, are conjugate:
`∀ rec a, F'rn (up ∘ rec ∘ down) (up a) = up (F rec a)`. Under any fixpoint semantics (and both
twins are compiled the same way) this gives equal fixpoints. A caller of a partial function is then
proved **modulo** that function's twin equation, which becomes an explicit hypothesis of the
caller's theorem (`proved_mod_partial`). Hypotheses propagate transitively through callers that are
themselves conditional.

The check runs only in memory. PALC appends `#twin_check` to each program it elaborates
(`lake exe palc`; `--no-twin` turns it off). The generated `.lean` files never contain twin
theorems. A pair that fails is reported and is never an error.

## Legitimate differences and how each is covered

| Difference between `f` and `f'rn` | Where it comes from | How it is covered |
|---|---|---|
| `List α` vs `Array α` | `_seq: "array"` stamp, O(1) runnable updates | **Proved**: bridge lemmas + loop conjugation (`Twin.lean`) |
| Bool `==`/`&&`/`!` vs Prop `=`/`∧`/`¬` conditions | Prop conditions are what `mvcgen`/`grind` want | **Proved**: `beq_twin`, `and_twin`, … (needs `LawfulBEq`) |
| `panic!` messages and source positions | each runtime function has its own | **Proved**: `panic! … = default` in the logic |
| user classes `C` vs `C'rn` | separate structures per twin | **Proved** (generated field-wise `TwinRel`); recursive classes (`Option C` fields) not yet |
| ℚ/ℝ vs `Float` | provability vs speed | **Not an equation.** Covered by the IEEE enclosure spec (`PastaLean/PyAPI/FloatInterval.lean`, proved `add_sound`/`mul…` enclosures) and refute's `ROUNDING_SENSITIVE`/`FLOAT_ONLY` verdicts |
| `x / 0`, out-of-range reads | the exact model returns a default; CPython raises | refute's `PARTIALITY_GAP`; both twins agree (both `default`), so the gap is between Lean and CPython, not between the twins |
| `assert` erased in `f'rn` | asserts are proof obligations of `f` | proved obligations hold on every input, so erasing them is sound for `f`; a failing *unproved* assert is a known gap (TODO: refute's `_asserts_raise`) |
| `PyProofM` (state model of IO) vs `IO`; `main'` vs `main''rn` | IO has no equational theory | **Trusted** IO model, exercised by stdin differential testing; reported as `monad` / `io_main` |
| `partial def` | no termination proof | **Step equivalence proved**; callers proved modulo it |
| `@cache` memo (`f'rn = (f'memo'rn ·).run' ∅`) | the runnable twin memoises | **Trusted** (`memo`); callers are proved modulo the memo pair's equation |
| `while` over `Array` state | core `while` is the opaque `Loop.forIn` | **Not provable** (`while`): an opaque loop cannot be conjugated. A `while` over identical state types *is* proved, by congruence |

## Measured coverage

PALC (`lake exe palc`, 186 programs, value semantics; the `--heap` examples are not checked yet). A
*pair* is one Python function's two Lean versions, `f` and `f'rn`; each is checked for `f'rn ≡ f` on
all inputs:

| | pairs |
|---|---|
| proved (`f'rn ∘ up = up ∘ f`) | **321** |
| proved assuming the twin equations of `partial` callees | 21 |
| `partial def`, step equivalence proved | 18 |
| float (ℚ/ℝ vs `Float`, not attempted: the relation is an enclosure) | 49 |
| IO entry point (`main` and its wrappers) | 117 |
| monad (`PyProofM` vs `PyExcept`/`IO`) | 39 |
| class (recursive class, or code using one) | 38 |
| memo | 4 |
| `while` over `Array` state | 2 |
| unproved, in scope | 4 |
| **total** | **613** |

Out of the 364 pairs whose types are related by `TwinRel`, 321 (88%) are proved outright, 342 (94%)
including those modulo `partial` callees, and 360 (99%) when step-equivalent `partial` pairs are
counted. The 4 remaining in-scope failures: `cube_fill` (a 3-D `Array (Array (Array Int))`, where the
nested-instance normal forms do not meet); `scalar_defaults` (a `float` default inside a
`defaultdict`: an internal float that the type signatures do not show); `sqrt_floor_plus_one` (an
internal ℝ/`Float` callee); `days_until` (a `datetime` library class).

Baseline, before this work: appending `example : @f = @f'rn := by first | rfl | (funext; simp
[f, f'rn]) | (simp only [f, f'rn]; decide)` proves 289 of the 466 pairs in the reviewed
`example_scripts/*/*.lean`. 39 of those 289 are the trivial `main` wrappers (`do let _ := …;
pure ()`), which are now classified `io_main`. On the same files, the checker proves 17 pairs the
naive tactic could not, plus 19 modulo `partial` callees and 14 step-equivalent `partial` pairs.

Cost: `#twin_check` adds about 3 s of elaboration over the 111 reviewed programs (≈12 s without
it). End-to-end, PALC wall time stays within the run-to-run noise of this machine (80 s without the
check, 71 s with it, in back-to-back runs). The check is therefore on by default.

The check also found a real bug. The `Array` `PyPrintable` instance rendered elements with `str`, so
`print(xs)` of an array-backed `list[str]` printed `[a, b]` where CPython prints `['a', 'b']`.
`pyStringify_array_twin` could not be proved until the instance was fixed. It now delegates to the
`List` instance (regression: `PALC/PyAPI/TestPyPrint.lean`).

## The trusted base

- Lean's kernel, and the axioms the twin theorems use (`propext`, `Quot.sound`,
  `Classical.choice` through Mathlib). There is no `sorry`, and nothing is axiomatised in
  `PastaLean/PyVerify/Twin/`.
- The Lean compiler: `f'rn` runs as compiled code, including `implemented_by` and `extern`
  runtime pieces (`Array.push` in place, `panic!`).
- The IO model: `PyProofM` agrees with real `IO` on the operations used (`input`, `print`).
- `partial def` and `while`: Lean compiles the opaque constants from the same bodies whose
  functionals we prove conjugate.
- The `Float` link: the enclosure spec bounds rounding error, but a proof over ℚ is a proof about
  the exact program only.
- The test link CPython ≈ `f'rn`.

## The codegen is auditable

The twins come from the same IR and the same generators. They diverge only where code generation asks
which twin it is emitting. There are **56 such switch points in 14 files** (`getNumericMode` and `numericModeIsExact`
call sites), each a row kind of the substitution table below; the `prim` sites read the table itself (the most are in `PyGens/UseCases/FuncDef.lean` (18),
`PyGens/Basic.lean` (8), `PyGens/UseCases/ClassDef.lean` (5), and `PyGens/Calls/*` (7)). Each one
is a place a reviewer can read to see what differs. Per-program translation validation then checks
that the difference is harmless for that program.

## The substitution table

Every difference between the twins is a row of one table, `PastaLean/PyVerify/Twin/Table.lean`
(`substTable`). Run `#twin_table` to print it. Each row has a kind:

| Kind | Meaning | How it is covered |
|---|---|---|
| `prim` | a runtime function replaced by another (`pyAppend ↦ pyArrayAppend`, …) | a bridge lemma `Twin.<run>_twin`, checked by `#twin_table` |
| `type` | a type replaced (`List ↦ Array`; `ℚ`/`ℝ ↦ Float`; the exception and IO monads) | `TwinRel` for `List`/`Array`; an IEEE enclosure for floats |
| `erase` | proof-only content (asserts as `have`, `_correct`/`_spec` theorems, `@[simp, taste_ingr]`) | no runtime content |
| `effect` | an effect the provable twin models (`print` on a stream) | trusted model, stdin differential testing |
| `transform` | a different algorithm in the runnable twin (memoisation) | open: needs one general lemma |

Code generation reads its `prim` substitutions from the table (`Twin.runPrim`), so the table and the
generated code cannot disagree. `#twin_table` reports each `prim` row: proved when its bridge lemma
`Twin.<run>_twin` is in the `@[twin]` set, rests on no `sorry`, and states the runnable primitive in
terms of the provable one; otherwise a warning, never an error (`PALC/Twin/Table.lean` runs it).

**Proving a pair against the table.** `twin% f` is the refinement statement for `f` and `f'rn`. The
tactic `twin_table` proves it by unfolding both twins and normalising with the `@[twin]` set. Before
that, it splits off everything the pair rests on that is not already proved, as named goals: a
`prim` row without a proved bridge lemma (`prim.<op>`), and a runnable callee whose own twin equation
is not proved (`callee.<g>`). What remains for the user is exactly the comparison of table entries
and callees:

```lean
def h (x : Int) : Int := g x * 2
def h'rn (x : Int) : Int := g'rn x * 2

theorem h_twin : twin% h := by
  twin_table
  case callee.g => intro x; simp only [g, g'rn]; omega   -- goal: ∀ x, g'rn x = g x
```

A `prim` row whose bridge lemma is not available gives one goal per instantiation the pair uses, in
the shape of the bridge lemma, over provable values (`pop` on an `Int` and on a `String` array are two
goals):

```lean
case prim.pyArrayPopValue_1  ⊢ ∀ (xs : List ℤ) (idx : ℤ), pyArrayPopValue xs.toArray idx = pyPopValue xs idx
case prim.pyArrayPopValue_2  ⊢ ∀ (xs : List String) (idx : ℤ), pyArrayPopValue xs.toArray idx = pyPopValue xs idx
case prim.pyArrayAppend      ⊢ ∀ (xs : List ℤ) (v : ℤ), pyArrayAppend xs.toArray v = (pyAppend xs v).toArray
```

The tactic itself never fails: whatever the normalisation does not close is left as a goal too. When
every primitive row is proved and every callee is already checked, `twin_table` alone closes the
goal (`addAll_twin` in `PALC/Twin/Table.lean`, an `Array`-state loop; the missing-lemma case is `PALC/Twin/MissingLemma.lean`).

## Towards one general theorem

Per-program validation is what we can do today. Every translated program comes with its own
kernel-checked refinement theorems. A single theorem of the form "for every Python program, the
twins agree" needs one of two things.

1. **Formalise the code generator.** Give a semantics to the JSON IR and prove that both emission
   modes refine it. That would mean verifying `PyGens` (≈ the whole Lean backend), which is large
   and still changing.
2. **Generate both twins from one definition.** Emit each function once, generic over a
   `PyModel` interface (the sequence type and its operations, the number type, the effect monad),
   and obtain `f` and `f'rn` as two instantiations. Agreement then follows from a parametricity-style
   argument plus **instance-level lemmas proved once in PastaLean's source**. Today's bridge lemmas
   are exactly those instance lemmas:
   - sequence ops: `pyArrayAppend_twin`, `pyArrayExtend_twin`, `pyArrayReverse_twin`,
     `pyArrayInsert_twin`, `pyArrayPopValue_twin`/`pyArrayPopRest_twin`,
     `pyArrayPopLeft*_twin`, `pyArrayRepeat_twin`, and `pyGetItem`/`pySetItem`/`pyModifyItem`/
     `pyLen`/`pySlice`/`pyContains`/`pyTruthy`/`PyBool`/`PyPrintable`/`pyClear`/`pyCount`/
     `pyIndex`/`pyIter` `_array_twin`;
   - element-wise containers: `pyGetItem_map_twin`, `pySetItem_map_twin`, `pyModifyItem_map_twin`,
     `pyAppend_map_twin` (with `TwinDefault`);
   - iteration: `forIn_twin`, `forIn'_twin`, `List.forIn_toArray`;
   - decisions: `beq_twin`, `bne_twin`, `and_twin`, `or_twin`, `not_twin`;
   - errors: `panic_twin`.

   The numeric and effect parameters are the parts that would stay outside: `Float` vs ℚ is not an
   equation, and `IO` vs `PyProofM` needs the IO model. With route 2, those two become the
   *entire* explicit trusted interface, and everything else is proved once rather than per program.
