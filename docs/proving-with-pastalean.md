# Proving the Lean that PastaLean emits

How to discharge the obligations `translate_python` (or `pastalean translate`) leaves open. Write
the contracts first (`docs/contract-prompt-system.md`); this file covers what comes after.

## What a translated file contains

For each Python function `f` with contracts, the output has:

| Declaration | What it is | You may edit |
|---|---|---|
| `def f` | the **provable twin**: exact `Int`/`ℚ`/`ℝ`, `List`, Python operators `+ₚ -ₚ *ₚ /ₚ %ₚ` | never |
| `@[spec] theorem f_spec` | the Hoare triple `⦃⌜pre⌝⦄ f args ⦃⇓r => ⌜post⌝⦄`, for monadic (loop / mutation) code | the proof only |
| `theorem f_correct` | the same property as a plain `∀ args, pre → post`; closes from `f_spec` automatically | the proof only |
| `def f'rn` | the **runnable twin** (`Float`/`Array`), for execution and differential testing | never |

Open obligations end in `taste?` (a proof-search tactic) or `sorry`. Your job is to replace that
proof. The rules, enforced by `verify_theorems`:

- Change only the text after `:= by`. Never change a `def` or a theorem's statement.
- You may add helper `theorem`s / `lemma`s (anywhere before their use). You may not add `def`,
  `instance`, `notation`, `macro`, `axiom`, or `set_option debug.skipKernelTC`.
- `sorry`, `admit` and `native_decide` do not count as proofs. Only the axioms `propext`,
  `Classical.choice`, `Quot.sound` are allowed.

## Pattern 1: a `for i in range(n)` loop

A working proof, emitted from `sum_to_n` (`Requires(n >= 0)`, `Invariant(2*total == i*(i-1))`,
`Ensures(2*total == n*(n+1))`):

```lean
@[spec] theorem sum_to_n_spec :
    ⦃⌜n ≥ (0 : Int)⌝⦄ sum_to_n n ⦃⇓total => ⌜(2:Int) *ₚ total = n *ₚ (n +ₚ (1:Int))⌝⦄ := by
  mvcgen [sum_to_n, pyRange_forIn, pyRange_forIn_start] invariants
  · ⇓⟨cur, total⟩ => ⌜(2:Int) * total = (cur.prefix.length : Int) * ((cur.prefix.length : Int) - 1)⌝
  all_goals simp_all [taste_ingr, pyRange]
  all_goals (first | omega | nlinarith | (ring_nf; omega) | grind)
```

The key points:

- `mvcgen [f, pyRange_forIn, pyRange_forIn_start]` unfolds `f` and rewrites `pyRange` loops into
  native `List.range` loops it knows how to step through.
- One `invariants` bullet per loop, in source order. The binder is `⇓⟨cur, <mutated vars…>⟩`.
  Copy the bullet the translator emitted and fix its body rather than writing one from scratch.
- **Restate the invariant over the cursor.** The Python loop variable is not in scope in the
  invariant. The number of finished iterations is `cur.prefix.length` (a `Nat`), so cast it:
  `(cur.prefix.length : Int)`. For `range(start, stop)`, the current element is
  `start + cur.prefix.length`.
- Then `simp_all [taste_ingr, …]` (`taste_ingr` unfolds the Python operators to Lean's) and a
  closer battery.

## Pattern 2: `range(start, stop)`, nested loops, lists

See `get_example("CountUpTo")`. It is a sieve with a nested loop and three postconditions about the
result list. Things it shows:

- A second, trivial bullet `· ⇓⟨cur, isprime⟩ => ⌜True⌝` for an inner loop that the property does
  not depend on.
- A helper lemma that recovers "current element = number of finished iterations" from the list
  split mvcgen produces:

  ```lean
  private theorem range_split_val {m : Nat} {pref suff : List Nat} {cur : Nat}
      (h : List.range m = pref ++ cur :: suff) : cur = pref.length := ...
  ```

- Targeting specific leftover goals with `case vc3.step.isTrue.post.success => …` after the
  `all_goals` sweep.

## Pattern 3: no loop (pure functions)

Non-monadic functions get a plain theorem. Unfold and close:

```lean
theorem strlen_correct : ∀ (string : String), strlen string ≥ (0 : Int) ∧ strlen string = PastaLean.pyLen string := by
  intro s
  refine ⟨?_, rfl⟩
  show (0 : Int) ≤ (String.length s : Int)
  omega
```

`simp [f, taste_ingr]` followed by `omega` / `ring` / `nlinarith` / `grind` closes most arithmetic.

## Reading the vocabulary

- **Operators.** Python `+ - * / // % **` are `+ₚ -ₚ *ₚ /ₚ` and friends. `taste_ingr` unfolds them to
  Lean operators. `//` and `%` are Python's *floor* division and modulo (`Int.fdiv`/`Int.fmod`
  semantics), not Lean's truncating ones; keep them folded unless you need their definition.
- **Quantified contracts.** `all(p(x) for x in xs)` becomes `∀ x ∈ pyIter xs, p x`. The simp lemmas
  `pyIter_list` (`pyIter l = l`) and `pyRange_mem` (`x ∈ pyRange n ↔ 0 ≤ x ∧ x < n`) reduce them to
  plain list and index facts.
- **Digging into the runtime.** When a goal mentions a runtime function (`pyLen`, `pyAppend`,
  `pySetItem`, `pyListRepeat`, …), find out what it computes before trying to prove anything about
  it: `find_definition("pyAppend")`, or `#print PastaLean.pyAppend` in a `check_lean` call. Then look
  for facts already proved about it: `search_lemmas("pyAppend")`, `grep_source("pyAppend")`. The
  layout: definitions in `PastaLean/PyAPI/` (`Core`, `Lists`, `Strings`, `Dicts`, `Sets`,
  `Builtins/`, `CommonProtocols/`); loop and contract lemmas in `PastaLean/PyVerify/`
  (`HelperLemmas.lean`, `PyWhile.lean`); library shims in `Libraries/`. If a fact you need is missing,
  prove it as a helper lemma in your file.
- **`while` loops** get an invariant bullet plus a termination measure from `Decreases(e)`.
  **`try`/`except`** translates to the `Except` monad, and `mvcgen` handles it the same way.

## When a proof will not close

1. **Check the property is true.** The most common failure is a *false postcondition*, not a weak
   proof. Evaluate the runnable twin on candidate inputs (`#eval f'rn 0`, `#eval f'rn (-1)`), or run
   `run_differential` with a `__main__` that prints edge cases. If it is false, fix the Python or its
   contract (that is a finding worth reporting), then re-translate.
2. **Strengthen the invariant.** An invariant must be inductive: strong enough that it implies itself
   after one more iteration, and that it implies the postcondition at the end. Most stuck `step`
   goals mean a fact is missing from it (a bound, a length, a relation to the loop index).
3. **Missing precondition.** If the property only holds for some inputs, the Python needs a
   `Requires`. That changes the spec, so edit the Python and re-translate.
4. **Isolate the goal.** Replace the closer battery with `all_goals sorry`, use `check_lean` to read
   the remaining goals, and prove each one with `case … =>`.
