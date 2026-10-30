import PastaLean.PyAPI.PyPanic
import PastaLean.Imports
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace Libraries.functools

/--
Runtime helper for `functools.reduce(function, iterable[, initializer])`.

The iterable comes first in the Lean helper so instance resolution can learn the
element type before elaborating the reducer lambda. That keeps overloaded arithmetic
inside generated lambdas much more predictable.
-/
def pyReduce {α β : Type} [inst : PastaLean.PyIterable α β] [Inhabited β] (xs : α)
    (f : β → β → β) (init : Option β := none) : β :=
  match init, PastaLean.pyIter xs with
  | some start, items => items.foldl f start
  | none, [] => PastaLean.pyPanic "TypeError: reduce() of empty iterable with no initial value"
  | none, x :: rest => rest.foldl f x

/-- `@cache`/`@lru_cache` is dropped — memoization is semantically transparent, we recompute — so the
cache-management methods the decorator adds (`f.cache_clear()`, `f.cache_info()`) lower to this
no-op. Correctness holds because nothing was memoised to go stale.

TODO: real memoization for the RUN twin only — a pure `opaque` signature + `@[implemented_by]` over an
ST/IO.Ref cache (never a state monad on the prove twin, which would cost provability). That would make
`cache_clear` a genuine mutation rather than a no-op. A speed feature; build it only if the eval pass
shows heavy-DP solutions timing out without it. -/
def pyCacheNoop : Unit := ()

/-- `functools.cmp_to_key(f)`. Python wraps `f` in a key object; there is no such object here — the
sort paths detect `key=cmp_to_key(f)` and use the comparator directly — so this is the identity,
present only so a bare reference to the name still resolves. -/
def pyCmpToKey {β : Type} (f : β → β → Int) : β → β → Int := f

end Libraries.functools
