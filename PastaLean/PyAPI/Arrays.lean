import PastaLean.PyAPI.PyPanic
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.Lists
import PastaLean.PyAPI.CommonProtocols.GetItem
import PastaLean.PyAPI.CommonProtocols.SetItem
import PastaLean.PyAPI.CommonProtocols.Length
import PastaLean.PyAPI.CommonProtocols.Membership
import PastaLean.PyAPI.CommonProtocols.Truthy
import PastaLean.PyAPI.CommonProtocols.Bool
import PastaLean.PyAPI.CommonProtocols.Clear
import PastaLean.PyAPI.CommonProtocols.Count
import PastaLean.PyAPI.CommonProtocols.Index
import PastaLean.PyAPI.CommonProtocols.Pop
import PastaLean.PyAPI.PyPrint

/-! # Array-backed sequences for the runnable (`'rn`) twin

Python `list` is a dynamic array — O(1) amortized append, O(1) index — but a `List α`-backed
`xs := xs ++ [v]` append is O(n) and `xs[i]` is O(i), so an append/index loop is O(n²) (validated:
`List` append+index at n=30000 ran ~134× slower than `Array`). The **provable** twin keeps `List α`
(Mathlib lemmas); the **runnable** (`'rn`) twin uses `Array α`, whose `push`/`set!`/`get!` are O(1)
when the array is uniquely owned — which the codegen's threaded mutation (`xs := pyArrayAppend xs v`,
reassigning the same binder) guarantees, so Lean's Perceus reference counting mutates in place.

Every op mirrors its `pyList*` / `List` protocol counterpart's Python semantics (negative indices,
`IndexError` on out-of-range) so the two twins agree on results. `List` remains the fallback: the
generated code is identical except for the binder type, so a value the codegen can't prove safe to
back with `Array` is simply stamped `List α` and uses the `List` instances instead. -/

namespace PastaLean

/-- O(1) indexed read with Python negative-index semantics (mirrors `pyListGetItem`). -/
def pyArrayGetItem {α : Type} [Inhabited α] (xs : Array α) (idx : Int) : α :=
  let len := xs.size
  if len == 0 then PastaLean.pyPanic "IndexError: list index out of range"
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then PastaLean.pyPanic "IndexError: list index out of range"
    else xs[trueIdx.toNat]!

/-- O(1) indexed write with Python negative-index semantics (mirrors the `PySetItem (List β)` body).
`Array.set!` mutates in place when `xs` is uniquely owned. -/
def pyArraySetItem {α : Type} (xs : Array α) (idx : Int) (v : α) : Array α :=
  let len := xs.size
  let lenInt : Int := len
  let trueIdx := if idx < 0 then lenInt + idx else idx
  if trueIdx < 0 || trueIdx >= lenInt then
    PastaLean.pyPanic "IndexError: list assignment index out of range"
  else xs.set! trueIdx.toNat v

/-- O(1) amortized append — in place when uniquely owned (`list.append`). -/
def pyArrayAppend {α : Type} (xs : Array α) (v : α) : Array α := xs.push v

/-- `[x] * n` sequence repeat: the (usually one-element) array `xs` concatenated `n` times. -/
def pyArrayRepeat {α : Type} (xs : Array α) (n : Int) : Array α :=
  if n ≤ 0 then #[] else Id.run do
    let mut out := Array.emptyWithCapacity (n.toNat * xs.size)
    for _ in [0:n.toNat] do
      out := out ++ xs
    return out

/-- `list.extend` / `a + b` concatenation. -/
def pyArrayExtend {α : Type} (xs ys : Array α) : Array α := xs ++ ys

/-- `list.reverse()` in place. -/
def pyArrayReverse {α : Type} (xs : Array α) : Array α := xs.reverse

/-- `list.insert(i, x)` — O(n) shift, so it borrows the `List` routine (mirrors `pyListInsert`). -/
def pyArrayInsert {α : Type} (xs : Array α) (idx : Int) (elem : α) : Array α :=
  (pyListInsert xs.toList idx elem).toArray

/-- The element `list.pop(idx)` returns (default last). O(1) for the last element (`.back!`);
a mid-list pop borrows the `List` routine so results match `pyPopValue` exactly. -/
def pyArrayPopValue {α : Type} [Inhabited α] (xs : Array α) (idx : Int := -1) : α :=
  if idx == -1 && xs.size > 0 then xs.back! else pyPopValue xs.toList idx

/-- The array after `list.pop(idx)` removes its element. O(1) drop-last (`.pop`); mid-list borrows
`pyPopRest`. -/
def pyArrayPopRest {α : Type} (xs : Array α) (idx : Int := -1) : Array α :=
  if idx == -1 && xs.size > 0 then xs.pop else (pyPopRest xs.toList idx).toArray

/-- `deque.popleft()` head element. -/
def pyArrayPopLeftValue {α : Type} [Inhabited α] (xs : Array α) : α :=
  if xs.size > 0 then xs[0]! else default

/-- `deque.popleft()` rest — O(n) head-drop (`Array` is a poor deque; correctness over speed here). -/
def pyArrayPopLeftRest {α : Type} (xs : Array α) : Array α := xs.toList.tail.toArray

instance {β : Type} [Inhabited β] : PyGetItem (Array β) Int β where
  getItem xs i := pyArrayGetItem xs i

instance {β : Type} : PySetItem (Array β) Int β where
  setItem xs i v := pyArraySetItem xs i v

/-- O(1) in-place nested update — `a[i] = f(a[i])`. `Array.modify` takes the element out (dropping its
refcount to 1), applies `f`, and puts it back, so `a[i][j] = v` is O(1), not an O(n) row copy. -/
instance {β : Type} [Inhabited β] : PyModifyItem (Array β) Int β where
  modifyItem xs idx g :=
    let sz : Int := xs.size
    let t := if idx < 0 then sz + idx else idx
    if t < 0 || t >= sz then PastaLean.pyPanic "IndexError: list assignment index out of range"
    else xs.modify t.toNat g

instance {α : Type} : PyLen (Array α) where
  pyLen xs := xs.size

/-- Slicing (`a[lo:hi:step]`) via `List` — inherently O(n), so an `Array`-backed sieve var may still
be sliced without dropping its O(1) index/write. -/
instance {β : Type} : PySlice (Array β) where
  slice xs lo hi step := (pyListSliceStep xs.toList lo hi step).toArray

instance {α : Type} [BEq α] : PyContains (Array α) α where
  contains xs x := xs.contains x

instance {α : Type} : PyTruthy (Array α) where
  truthy xs := !xs.isEmpty

instance {α : Type} : PyBool (Array α) where
  pyBool xs := xs.size != 0

instance {α : Type} [PyPrintable α] : PyPrintable (Array α) where
  pyStringify xs := "[" ++ String.intercalate ", " (xs.toList.map pyStringify) ++ "]"

instance {α : Type} : PyClear (Array α) where
  pyClear _ := #[]

instance {α : Type} [DecidableEq α] : PyCount (Array α) α where
  pyCount xs elem := pyListCount xs.toList elem

instance {α : Type} [DecidableEq α] : PyIndex (Array α) α where
  pyIndex xs elem start :=
    if start ≤ 0 then pyListIndex xs.toList elem
    else match pyListIndex (xs.toList.drop start.toNat) elem with
      | -1 => -1
      | i => i + start

end PastaLean
