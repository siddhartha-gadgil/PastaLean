import PastaLean.Imports

/-- `@[twin]`: the simp set the `twin` tactic normalises with — bridge lemmas rewriting the runnable
(`'rn`) twin's runtime into the provable twin's, plus every proved `f_twin_eq`. Registered in its own
module since an attribute can't be used where it's registered. -/
register_simp_attr twin
