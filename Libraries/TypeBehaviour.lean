import TypeInfer.PyType
import Libraries.Behaviour

/-!
# Type-inference behaviour — the Mathlib-free half of the library `Behaviour` records

`TypeInfer` needs only two of a `Behaviour` record's fields — `returns` and `teaches?` (the ones
tagged `[inference]`). The `[codegen]` fields (`mutator`/`keyedVariant`/…) carry *checked* runtime
names (`` ``pyHeapify ``), which drag each library's runtime shim — and, transitively, Mathlib — into
the import closure. Elaborating those names is a code-generation concern the type engine never reads.

So the pure return-shape behaviour of every library member lives here, importing only `PyType` and the
combinators — no runtime, no Mathlib. `Libraries/*/Mapping.lean` keeps the full records (behaviour +
codegen names) for the code generator; `Registry` aggregates those. This module aggregates the
type-only view (`memberTypeBehaviour?`/`bareTypeBehaviour?`/`libraryMemberReturn?`) that
`TypeInfer/Rules.lean` consumes, so the inference engine builds free of the runtime.

Members whose only behaviour is a mutation or a keyed-variant (`heapq.heapify`, all of `bisect`) carry
no `returns`/`teaches?`, so they are simply absent here — the type engine learns nothing from them.
-/

namespace Libraries.math
open Libraries

/-- Return type of a `math` member, for TypeInfer. Mode-agnostic (`.float` becomes `ℚ`/`ℝ`/`Float`
in codegen per numeric mode; transcendentals go to `ℝ` via the real-flow pass). -/
def mathBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  if ["sqrt", "sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "exp", "log",
      "log2", "log10", "fabs", "pow", "atan2", "hypot", "expm1", "log1p", "copysign", "fmod",
      "dist", "radians", "degrees"].contains member then some (const .float)
  else if ["floor", "ceil", "trunc", "factorial", "gcd", "lcm", "isqrt", "comb", "perm",
           "prod"].contains member then some (const .int)
  else if ["isnan", "isinf", "isfinite"].contains member then some (const .bool)
  else none

end Libraries.math

namespace Libraries.numpy
open Libraries

/-- Peel a nested list to its scalar element (`List (List ℚ)` → `ℚ`). -/
partial def scalarField : TypeInfer.PyType → TypeInfer.PyType
  | .list e => scalarField e
  | t => t

/-- numpy member behaviour — the return type as a function of the FIRST argument's type, since the
shims are polymorphic over the field (`np.dot` of `ℚ` vectors gives `ℚ`). `none` = let Lean infer it.
Reductions/elementwise/creators always return `Float` (never the caller's `ℚ`), so they are omitted
and left for Lean to infer — forcing `ℚ` in exact mode would clash with the shim. -/
def numpyBehaviour? (member : String) : Option Libraries.Behaviour :=
  let ofArg0 (f : TypeInfer.PyType → TypeInfer.PyType) : Libraries.Behaviour :=
    { returns := fun as => f ((as[0]?).getD .unknown) }
  -- `dot` is the one field-scalar reduction (`… → γ`): result = the arg's scalar field.
  if member == "dot" then some (ofArg0 scalarField)
  -- Field-preserving matrix ops (`… → List (List α)`): result has the arg's shape and field.
  else if ["add", "subtract", "multiply", "scale", "matmul"].contains member then some (ofArg0 id)
  else if ["argmax", "argmin", "searchsorted"].contains member then some (ofArg0 fun _ => .int)
  else if ["argsort", "nonzero", "shape"].contains member then some (ofArg0 fun _ => .list .int)
  else if ["any", "all"].contains member then some (ofArg0 fun _ => .bool)
  else none

end Libraries.numpy

namespace Libraries.scipy

/-- Return type of a `scipy` member, for TypeInfer (all `.float` in this supported subset). -/
def scipyBehaviour? (member : String) : Option Libraries.Behaviour :=
  if ["factorial", "comb", "perm", "gamma", "erf", "pi", "golden", "golden_ratio", "tmean",
      "gmean", "hmean", "norm", "det"].contains member then some (Libraries.Behaviour.const .float)
  else none

end Libraries.scipy

namespace Libraries.itertools
open Libraries TypeInfer

/-- itertools members' return shapes (`chain` → list of the args' common element type; `product` →
list of Cartesian-product tuples; `accumulate` → running fold; `pairwise` → consecutive
`(elem, elem)` pairs), and the unbounded-iterator shape for the desugarer (`count`/`cycle`/`repeat`). -/
def itertoolsBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "chain"      => some listOfJoined
  | "product"    => some listOfTuples
  | "accumulate" => some (listOf 0)
  | "pairwise"   => some adjacentPairs
  | "count"      => some { infiniteIter := some .counter }
  | "cycle"      => some { infiniteIter := some .cyclic }
  | "repeat"     => some { infiniteIter := some .constant }
  | _ => none

end Libraries.itertools

namespace Libraries.collections
open Libraries TypeInfer

/-- Return-type behaviour of `collections` constructors: `Counter(xs)` is a `dict[elem, int]`;
`deque(xs)` a list of `xs`'s element; `OrderedDict(d)` passes its dict through. (`defaultdict` reads
its factory ARGUMENT's name, not a type, so it stays in the engine's `builtinReturn`.) -/
def collectionsBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "Counter"     => some (counterOf 0)
  | "OrderedDict" => some (argType 0)
  | "deque"       => some (listOf 0)
  | _ => none

end Libraries.collections

namespace Libraries.functools
open Libraries

/-- Behaviour of the `functools` members the core codegen must know something extra about.
`cmp_to_key` turns a 3-way comparator into a sort key, which has no runtime object here — the sort
paths unwrap it and use the comparator directly. -/
def functoolsBehaviour? (member : String) : Option Behaviour :=
  match member with
  | "cmp_to_key" => some { cmpKeyWrapper := true }
  | _ => none

end Libraries.functools

namespace Libraries.hashlib
open Libraries

/-- `md5(...)` carries the message through and `hexdigest()` digests it, so both are `str`. The
constructors also declare `constructsObject`, so `m = hashlib.md5()` makes `m.update(...)` dispatch
here instead of to the dict/set `update`. -/
def hashlibBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "md5" | "sha256" => some { const .str with constructsObject := true }
  | "hexdigest" | "digest" | "update" => some (const .str)
  | _ => none

end Libraries.hashlib

namespace Libraries.json
open Libraries

/-- `loads` yields a dynamic value (`PyAny`); `dumps` a `str`. -/
def jsonBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "loads" => some (const .any)
  | "dumps" => some (const .str)
  | _ => none

end Libraries.json

namespace Libraries.sortedcontainers
open Libraries TypeInfer

/-- `SortedList(xs)` yields a list of `xs`'s element type (it IS a sorted `List`). -/
def sortedcontainersBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "SortedList" => some (listOf 0)
  | _ => none

end Libraries.sortedcontainers

namespace Libraries.heapq
open Libraries

/-- Type-only view of `heapq` members — the mutation/keyed-variant codegen names stay in
`heapq/Mapping.lean` (`heapqBehaviour?`); this is what inference reads. `heapify` teaches nothing. -/
def heapqTypeBehaviour? (member : String) : Option Behaviour :=
  open Behaviour in
  match member with
  | "heappush"    => some (push 0 1)
  | "heappop"     => some (elementOf 0)
  | "heapreplace" => some (elementOf 0)
  | "heappushpop" => some { elementOf 0 with teaches? := (push 0 1).teaches? }
  | "nlargest"    => some (listOf 1)
  | "nsmallest"   => some (listOf 1)
  | _ => none

end Libraries.heapq

namespace Libraries
open TypeInfer

/-- Type behaviour of a qualified library member `mod.member`, for TypeInfer. The codegen twin is
`Registry.memberBehaviour?` (full records with mutator names). -/
def memberTypeBehaviour? (moduleName member : String) : Option Behaviour :=
  match moduleName with
  | "heapq"       => heapq.heapqTypeBehaviour? member
  | "itertools"   => itertools.itertoolsBehaviour? member
  | "collections" => collections.collectionsBehaviour? member
  | "bisect"      => none  -- bisect members carry only codegen behaviour (mutator/keyedVariant)
  | "functools"   => functools.functoolsBehaviour? member
  | "hashlib"     => hashlib.hashlibBehaviour? member
  | "json"        => json.jsonBehaviour? member
  | "math"        => math.mathBehaviour? member
  | "scipy"       => scipy.scipyBehaviour? member
  | "numpy"       => numpy.numpyBehaviour? member
  | "sortedcontainers" => sortedcontainers.sortedcontainersBehaviour? member
  | _ => none

/-- Type behaviour of a bare (unqualified) name — a builtin, or a `from itertools import count`-style
name. `bisect` omitted: its bare members contribute no return/teaches type. -/
def bareTypeBehaviour? (name : String) : Option Behaviour :=
  (builtinBehaviour? name).orElse fun _ =>
  (itertools.itertoolsBehaviour? name).orElse fun _ =>
  (heapq.heapqTypeBehaviour? name).orElse fun _ =>
  (collections.collectionsBehaviour? name).orElse fun _ =>
  (functools.functoolsBehaviour? name)

/-- Return type of a qualified library member, for TypeInfer (`.unknown` → `none`, as before). -/
def libraryMemberReturn? (moduleName member : String) (arg0 : TypeInfer.PyType) :
    Option TypeInfer.PyType :=
  match (memberTypeBehaviour? moduleName member).map (·.returns [arg0]) with
  | some t => if t == .unknown then none else some t
  | none => none

end Libraries
