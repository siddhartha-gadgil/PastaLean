import PastaLean
import Std.Tactic.Do

/-!
# `example_scripts/heap/14_bank_account.py` — framed separation-logic specs

`def`s copied verbatim from

    pastalean translate example_scripts/heap/14_bank_account.py --heap --no-check

(proof-mode declarations only; `amount` annotated `Int`). `deposit` is a read/modify/write, and
`withdraw` guards its write on a read of `self` — both frame a disjoint account `other ↦ o`
automatically, and `withdraw`'s spec carries the branch condition into the postcondition.

`demo` runs the whole `main`: allocate an account at 100, alias it, deposit 50, withdraw 30, then
attempt an over-withdrawal of 1000 (insufficient → no-op), and read the balance back — which is
`120`. `demo_spec` proves that concrete value: the returned fact `⌜r = 120⌝` floats out of the
freshly-allocated heap through every `…M` call and the conditional withdrawal.

No per-file boilerplate: the `⌜·⌝` floaters and `+ₚ`/`-ₚ` grind lemmas are `scoped` to `PastaLean`
in `Proof.lean`, so `open PastaLean` brings them in.

This module stays at the root namespace (as the translator emits) and is built as an independent
compilation unit (lakefile `globs`), so its `Val` never collides with another example's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 0

structure BankAccount where
  balance : Int
  deriving Inhabited, Repr, BEq

inductive Val where
  | bankAccount (balance : Int)
  deriving Repr, Inhabited

derive_storable% BankAccount

def BankAccount.new := fun (balance : Int) ↦
  ((do
      PastaLean.alloc ({ balance := balance } : BankAccount)) :
    PastaLean.HeapM Val (PastaLean.Ref BankAccount))

def BankAccount.deposit (self : PastaLean.Ref BankAccount) (amount : Int) :=
  ((do
      self ~> balance <~ (← (self ~> balance)) +ₚ amount) :
    PastaLean.HeapM Val Unit)

def BankAccount.withdraw (self : PastaLean.Ref BankAccount) (amount : Int) :=
  ((do
      if h_1 : amount ≤ (← (self ~> balance)) then
        self ~> balance <~ (← (self ~> balance)) -ₚ amount
      else
        let _ := ()) :
    PastaLean.HeapM Val Unit)

def BankAccount.balance_of (self : PastaLean.Ref BankAccount) :=
  ((do
      let __py_ret_1 := (← (self ~> balance))
      return __py_ret_1) :
    PastaLean.HeapM Val _)

/-- Depositing into `self` adds to its balance and frames a joint handle `other ↦ o`. -/
theorem BankAccount.deposit_spec (self other : Ref BankAccount) (b o : BankAccount) (amount : Int) :
    ⦃ (self ↦ b ∗ other ↦ o : HProp Val) ⦄ BankAccount.deposit self amount
    ⦃ fun _ => self ↦ { b with balance := b.balance +ₚ amount } ∗ other ↦ o ⦄ := by
  vcgen [BankAccount.deposit, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish

/-- Withdrawal is conditional on the read balance; either branch frames `other ↦ o`. The
postcondition mirrors the guard: debit on success, no change when funds are insufficient. -/
theorem BankAccount.withdraw_spec (self other : Ref BankAccount) (b o : BankAccount) (amount : Int) :
    ⦃ (self ↦ b ∗ other ↦ o : HProp Val) ⦄ BankAccount.withdraw self amount
    ⦃ fun _ => self ↦ (if amount ≤ b.balance then { b with balance := b.balance -ₚ amount } else b)
      ∗ other ↦ o ⦄ := by
  vcgen [BankAccount.withdraw, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish

/-- The getter is read-only and frames both its own cell and a disjoint `other ↦ o`. -/
theorem BankAccount.balance_of_frame (self other : Ref BankAccount) (b o : BankAccount) :
    ⦃ (self ↦ b ∗ other ↦ o : HProp Val) ⦄ BankAccount.balance_of self
    ⦃ fun _ => self ↦ b ∗ other ↦ o ⦄ := by
  vcgen [BankAccount.balance_of, readRefM_spec] simplifying_assumptions with finish

def demo :=
  ((do
      let mut acc := (← BankAccount.new (100 : Int))
      let mut shared := acc
      let _ ← BankAccount.deposit acc (50 : Int)
      let _ ← BankAccount.withdraw shared (30 : Int)
      let _ ← BankAccount.withdraw shared (1000 : Int)
      let __py_ret_1 := (← BankAccount.balance_of acc)
      return __py_ret_1) :
    (PastaLean.HeapM Val) _)

/-- The whole `main`: alloc at 100, alias, `+50`, `-30`, an over-withdrawal of 1000 that no-ops on
insufficient funds, then read back — `120`. The value fact floats out of the fresh heap. -/
theorem demo_spec :
    ⦃ (emp : HProp Val) ⦄ demo ⦃ fun r => (⌜r = (120 : Int)⌝ : HProp Val) ⦄ := by
  vcgen [demo, BankAccount.new, BankAccount.deposit, BankAccount.withdraw, BankAccount.balance_of,
    alloc_frame_spec, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish
