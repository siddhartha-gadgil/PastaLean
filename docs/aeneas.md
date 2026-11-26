# Aeneas (Rust → Lean): how it works, why it matters, what PastaLean can learn

Research notes, November 2026. Sources: the AeneasVerif repositories (cloned at HEAD, 20 Nov 2026),
the papers, the Microsoft Research blog posts and the 2026 SymCrypt technical report
(arXiv 2609.15648). Figures are quoted from those sources, not re-derived; items marked
**(unverified)** had weak or conflicting sourcing.

## 1. What it is

Aeneas translates **safe Rust** into **pure functional code** in Lean 4 (also F\*, Coq/Rocq and HOL4;
Lean is now the main backend). Properties are then proved about that model in ordinary Lean, with
Mathlib available. Proofs are *extrinsic*: they live in separate files, and the Rust needs no
annotations.

The founding insight: **Rust's ownership discipline removes the need for a memory model.** In safe
Rust no two live mutable references alias, so a program can be translated into a pure function with no
heap and no separation logic.

**People.** Started by Son Ho during his PhD at Inria Paris (Prosecco team), supervised by Karthikeyan
Bhargavan and Jonathan Protzenko; repositories created Oct–Nov 2021. Current members
(aeneasverif.github.io/people): Son Ho (Microsoft Azure Research), Aymeric Fromherz (Inria), Jonathan
Protzenko (Google), Guillaume Boisseau (Inria; main Charon author), Oliver Butterley, Matej Penciak,
Jacob Prinz, Haoyi Zeng (Beneficial AI Foundation), Cezar Andrici (PhD intern, Azure Research).
Alumni: Sidney Congard, Ryan Lahfa, Yoann Prak, Fernando Leal (Inria), Remy Seassau, Mantas Baksys
(Azure Research). GitHub: `aeneas` ~1.2k stars, 50 contributors; `charon` ~490 stars.

## 2. How it is implemented

### Front end: Charon (Rust → LLBC)

Charon is a `rustc` driver (~18k lines plus a vendored part of Cryspen's hax exporter). It reads the
compiler's own MIR, so moves, drops and reborrows are exactly what rustc decided, and produces:

1. **ULLBC** (Unstructured Low-Level Borrow Calculus): a cleaned-up control-flow graph. Passes rebuild
   `match`es from discriminant switches, fold `panic!` desugarings and overflow asserts back into
   checked operations, recover constants, `Box` and `vec![]`.
2. **LLBC**: the same statements as a structured AST (`loop`, `break`/`continue` to depth, `if`,
   `match`, `return`), reconstructed with dominators (`ullbc_to_llbc.rs`); irreducible graphs are
   rejected.

Trait uses are resolved into explicit dictionaries (`TraitRef` = an impl, a where-clause, or an
implied clause). Output is JSON, read from OCaml (`charon-ml`) or Rust. Charon is now shared
infrastructure: Eurydice (Rust → C), hax's Lean backend, Soteria-Rust and Kani use it.

Supported now: `dyn Trait`, GATs, higher-ranked bounds, closures, `Drop`, unsafe code (extracted, but
Aeneas cannot translate it). Open: `async`, `CoerceUnsized`, contracts.

### Core: symbolic execution over borrows

Aeneas (OCaml) runs a **symbolic interpreter** over LLBC:

- A mutable borrow is a marker `borrow ℓ v`; the owner's place becomes `loan ℓ`. Shared borrows keep
  the value at the lender.
- At a call, each lifetime of the callee becomes a **region abstraction**: a bag of loans (borrowed
  inputs) and borrows (returned references).
- Borrows end lazily. Ending an abstraction returns values to their owners; in the translation, that
  return is a **backward function**.

`fn choose<'a>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` becomes

```lean
def choose (b : Bool) (x y : T) : Result (T × (T → T × T)) :=
  if b then ok (x, fun z => (z, y)) else ok (y, fun z => (x, z))
```

The result comes with a closure that pushes an updated value back into `x` or `y` (a lens-like
"backward function"). Shared borrows become plain values; `Box` is the identity.

**Loops** (ICFP 2024): a *join* of symbolic states (inspired by abstract interpretation and shape
analysis) plus a *collapse* step, then a fixed point up to renaming. The authors say plainly that they
do not claim termination and that collapse relies on heuristics. Each loop becomes its own `_loop`
function defined with Lean's `partial_fixpoint`; divergence is a value of the monad, termination is
proved separately when needed.

### The Lean library and tactics (`backends/lean/Aeneas/`, ~45k lines)

- `Result` with `ok` / `fail` / `div`; recently reimplemented as an interaction tree (`ITree
  RustEffect`), groundwork for effects.
- Machine integers are bitvector-backed (`U32` …); every operation that can overflow returns a
  `Result`. `Vec`, `Slice`, `Array` are modelled over lists.
- The standard library is modelled by hand. Each model carries its Rust path
  (`@[rust_fun "alloc::vec::…"]`) and the extractor's name table is regenerated from those tags: the
  Lean library is the single source of truth for name mapping.
- Specs are Hoare-style: `f x ⦃ r => P r ⦄`.
- **`step`** (formerly `progress`) handles the first monadic call by applying that call's registered
  `@[step]` spec lemma (lemmas indexed by the call term) and discharges side conditions in phases
  (assumption, then simp/grind/arithmetic). `step*` repeats through a function; `step*?` prints the
  expanded script.
- Solvers and rewriters: `scalar_tac` (`omega` with integer bounds and forward rules), `bv_tac`
  (bitvectors + `bv_decide`), `simp_lists`, `simp_scalar`, `agrind` (restricted `grind`),
  `natify`/`zmodify`, `#decompose` (split a long function into helpers, with the equation proved).

A real proof (`tests/lean/Demo/Properties.lean`):

```lean
def mul2_add1 (x : Std.U32) : Result Std.U32 := do
  let i ← x + x
  i + 1#u32

theorem mul2_add1.spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : mul2_add1 x ⦃ y => y.val = 2 * x.val + (1 : Nat) ⦄ := by
  unfold mul2_add1
  step as ⟨ i ⟩
  step as ⟨ i' ⟩
  scalar_tac
```

Loop specs are proved by recursion on the spec theorem itself, with `termination_by` and
`decreasing_by scalar_decr_tac`.

## 3. The soundness story

- **ICFP 2022**, "Aeneas: Rust Verification by Functional Translation" (Ho, Protzenko): defines LLBC,
  its symbolic version, and the translation with backward functions. The translation is **not**
  proved correct.
- **ICFP 2024**, "Sound Borrow-Checking for Rust via Symbolic Semantics" (Ho, Fromherz, Protzenko):
  proves, on paper, that the symbolic interpreter is a sound borrow checker against a CompCert-style
  low-level model (forward simulations), loops included. It explicitly leaves correctness of the
  translation to Lean as future work. Mechanisation is in progress.
- **CAV 2025**, "Charon: An Analysis Framework for Rust".
- Son Ho's thesis (PSL, 2024): accessit, GDR Sécurité prize (2025) and Gilles Kahn prize (2026).
- The 2026 report states the **trusted base**: rustc and its back ends, Charon, the Aeneas
  translation, the standard-library models, the Lean specifications of the standards, and the Lean
  kernel. Proofs are not trusted.

The lesson: a careful, partial correctness argument plus an explicit list of what is trusted.

## 4. What it has verified

- **Early case studies**: a resizable hash table (ICFP 2022, "the first such result in Rust") and a
  B-epsilon tree (later dropped from the tests).
- **Microsoft SymCrypt** (the cryptographic library in Windows, Azure Linux and Xbox), the flagship:
  - June 2025: Microsoft announces the rewrite of SymCrypt in Rust, verified with Aeneas and Lean,
    compiled to C with Eurydice for compatibility.
  - July 2026: SHA-3 and ML-KEM fully proved; per Azure CTO Mark Russinovich, running in **Windows
    Insider builds**. Specs and proofs open-sourced (SymCrypt branch `feature/verifiedcrypto`).
  - September 2026 report: 16.7k lines of Rust verified for safety, panic-freedom and functional
    correctness (16 algorithms incl. SHA-2/3, AES-GCM, HMAC, HKDF, ML-KEM, ML-DSA, FrodoKEM, HPKE;
    x86-64 and ARM, SIMD). 237k lines of Lean: ~30k generated, ~207k written (≈26k specifications
    formalised from NIST/IETF standards, ≈52k properties, ≈125k tactic proofs).
  - **AI agents wrote about 125k lines of proof (~5.1k theorems)**; humans wrote and gated specs and
    axioms; agents could not change specs, axioms or code without approval. Reported cost: "a few
    dollars per Rust LOC verified (high variance)". Model details in the report are
    **(unverified)** here.
  - Three real bugs found (SHA-3 output extraction, an ML-KEM NTT bound `x<Q` vs `x≤Q`, a FrodoKEM
    constant-time compare shift). The verified Rust matches or beats the C.
- **curve25519-dalek** (Beneficial AI Foundation): 288 functions of the serial 64-bit backend; one
  documentation precondition gap found. Date **(unverified)**, most likely 2026.
- **Signal Shot** (April 2026): Signal, BAIF and the Lean FRO aim to verify the Signal protocol's Rust
  implementation with Aeneas.
- Others: zkEVM components (Plonky3, RISC Zero; Ethereum Foundation via Runtime Verification), a
  Google jxl-rs case study, Mistral's Leanstral 1.5 (11 real bugs across 57 repositories, Mistral's
  own figures).
- **Benchmark substrate**: Aegis (Oct 2026), ~2k Rust–Lean pairs built from Aeneas output, labels
  kernel-checked proofs *or refutations*; BAIF's `auto_verify_dalek`. LLM provers now target Aeneas
  output.

## 5. Why it became famous

1. **A flagship industrial result in shipping software** (SymCrypt in Windows).
2. **A clean, easily stated idea**: ownership ⇒ no separation logic ⇒ Lean and Mathlib apply.
3. **Strong papers**: ICFP twice, CAV, a prized thesis.
4. **Endorsement from the Lean ecosystem**: an official use-case page on lean-lang.org; Leo de Moura:
   "When the Aeneas team tells you what's slow, you fix it."
5. **Deliberately the default AI-proving target**: the repository ships a `CLAUDE.md`, ~5.4k lines of
   agent skills, campaign rules ("statements first", "never turn a `sorry` into an axiom", banned
   tactics), dashboards, and a "fix the library spec, not the proof" rule for the standard library.

## 6. Limitations

- No unsafe code (raw pointers), interior mutability (`Cell`, `RefCell`, `Mutex`), concurrency, I/O
  or `async`; such functions are modelled by hand. A separation-logic layer is planned.
- Unsupported control flow: `return` inside nested loops, `break` to an outer loop; instantiating a
  generic with a mutable reference.
- Loop handling is heuristic and can fail.
- No floating point.
- The translation to Lean is trusted, not proved.

## 7. Day-to-day workflow worth copying

- Generated files (`Types.lean`, `Funs.lean`) are never edited; external functions go in a
  `FunsExternal_Template.lean` copied once to `FunsExternal.lean` (axioms only for opaque items).
- SymCrypt's `make extract` pins Charon/Aeneas commits and the rustc nightly, writes a provenance
  record, refuses a Lean toolchain mismatch, and diffs templates instead of overwriting.
- BAIF's dalek project tracks each function as extracted / draft spec / specified / verified in a
  `status.csv` that drives a dashboard; Rust edits needed for extraction are kept as a diff.
- Every standard-library model has a `.spec` lemma usable by `step` unaided, and its documentation
  examples become `#guard` tests run by `lake build`.

## 8. PastaLean side by side

| | Aeneas | PastaLean |
|---|---|---|
| Key enabler | Ownership makes a pure model possible | Type inference, functional threading of mutation, heap tier for aliasing |
| Models | One (`Result`, machine integers) | Two twins (exact `ℚ`/`List` vs `Float`/`Array`), plus CPython |
| Twin agreement | n/a | Checked per program in Lean (`PastaLean/PyVerify/Twin/`, `docs/trust.md`) |
| Effects | None yet (groundwork) | Exceptions and IO (stream model) |
| Floats | None | IEEE enclosures, `FLOAT_ONLY` / `ROUNDING_SENSITIVE` verdicts |
| Bug finding | External (Leanstral, Aegis refutation labels) | Built in: `pastalean refute`, kernel-checked counterexamples, 32/32 on CrossHair's benchmark |
| Proof automation | `step`, `scalar_tac`, curated simp sets | `taste?` portfolio, `mvcgen` for loops |
| Soundness argument | ICFP 2024 (borrow checking); translation trusted | `docs/trust.md` (in progress) |
| Flagship application | SymCrypt in Windows | None yet |
| AI workflow | Skills, campaign rules, dashboards | MCP server, `verify-python` skill |

## 9. What PastaLean should do

1. **Trust story** (our counterpart to ICFP 2024): an explicit aliasing discipline (when a Python list
   may be translated functionally, when the heap tier or a rejection is required); twin agreement by
   construction (one substitution table, general refinement lemmas in source, a per-program
   certificate); the CPython link stays tested; an explicit trusted base.
2. **A flagship application**: pure-Python reference implementations of standards (ML-KEM, ML-DSA,
   SHA-3 reference code; RFC reference implementations) against Lean specs of the standards, with
   known-answer `#guard` tests. Or CPython's pure-Python standard library modules against their
   documentation.
3. **Libraries from source**: translate the pinned pure-Python CPython sources (`bisect`, `heapq`,
   `json`, `_pydatetime`, …) with a never-edited generated file, an overrides file, and a provenance
   record; C-backed libraries stay hand-written for now.
4. **A spec library for the runtime**: a spec lemma per `PyAPI` function in the shape `mvcgen` /
   `taste?` apply unaided, documentation examples as `#guard` tests, curated simp/grind sets.
5. **Agent-campaign tooling**: statements before proofs, no new axioms, decompose rather than
   axiomatise, a per-function status file, proof replay on regeneration.
6. **Publish PastaBench as a benchmark** with proof labels *and* kernel-checked refutation labels.
7. **Lean into what Aeneas lacks**: floats, IO, exceptions, built-in bug finding.

## Sources

- https://aeneasverif.github.io/ (people, publications, projects, in the news, newsletters)
- https://github.com/AeneasVerif/aeneas, https://github.com/AeneasVerif/charon (incl. issue #142,
  `docs/limitations.md`)
- ICFP 2022: https://arxiv.org/abs/2206.07185, https://dl.acm.org/doi/10.1145/3547647
- ICFP 2024: https://arxiv.org/abs/2404.02680, https://dl.acm.org/doi/10.1145/3674640
- Charon, CAV 2025: https://arxiv.org/abs/2410.18042
- Son Ho's thesis: https://theses.hal.science/tel-05004605 ; https://www.sonho.fr/2026/03/18/aeneas-overview.html
- SymCrypt report: https://arxiv.org/abs/2609.15648 ; https://github.com/microsoft/SymCrypt/tree/feature/verifiedcrypto/SymCRust
- https://www.microsoft.com/en-us/research/blog/rewriting-symcrypt-in-rust-to-modernize-microsofts-cryptographic-library/
- https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/
- https://lean-lang.org/use-cases/aeneas/
- https://leodemoura.github.io/blog/2026-4-20-signal-shot-the-platform-is-ready/ ; https://leodemoura.github.io/blog/2026-4-2-why-lean/
- https://jonathan.protzenko.fr/2026/05/05/jxl-rs.html ; https://jonathan.protzenko.fr/2025/10/28/eurydice.html
- https://www.beneficialaifoundation.org/blog/curve-dalek ; https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
- https://hax.cryspen.com/blog/2026/09/29/hax-04-easier-to-install-and-configure-and-a-new-lean-backend/
- https://arxiv.org/abs/2605.30106 (Runtime Verification / Ethereum Foundation) ; https://arxiv.org/abs/2610.38174 (Aegis / EasyProver)
- https://mistral.ai/news/leanstral-1-5/
