import Lean
import Libraries.Mutator
import Libraries.Behaviour
-- The pure return-shape halves of each library's behaviour (`math.mathBehaviour?`, …) live here now;
-- the full `memberBehaviour?` below reuses them and adds the codegen (mutator/keyed-variant) fields.
import Libraries.TypeBehaviour
import Libraries.bisect.Mapping
import Libraries.collections.Mapping
import Libraries.functools.Mapping
import Libraries.hashlib.Mapping
import Libraries.json.Mapping
import Libraries.re.Mapping
import Libraries.datetime.Mapping
import Libraries.heapq.Mapping
import Libraries.itertools.Mapping
import Libraries.math.Mapping
import Libraries.operator.Mapping
import Libraries.string.Mapping
import Libraries.numpy.Mapping
import Libraries.passta.Mapping
import Libraries.random.Mapping
import Libraries.scipy.Mapping
import Libraries.pandas.Mapping
import Libraries.sortedcontainers.Mapping

namespace Libraries

/--
Registry mapping imported Python library members to Lean runtime functions/constants.

This plays the same role for imported libraries that `PastaLean.Attributes` plays for
Python methods: codegen consults this table once an AST node has been recognized as
coming from a specific imported module.
-/
def pythonLibraryMap? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "bisect" => bisect.pythonBisectMemberMap? member
  | "collections" => collections.pythonCollectionsMemberMap? member
  | "functools" => functools.pythonFunctoolsMemberMap? member
  | "hashlib" => hashlib.pythonHashlibMemberMap? member
  | "json" => json.pythonJsonMemberMap? member
  | "re" => re.pythonReMemberMap? member
  | "heapq" => heapq.pythonHeapqMemberMap? member
  | "itertools" => itertools.pythonItertoolsMemberMap? member
  | "math" => math.pythonMathMemberMap? member
  | "operator" => operator.pythonOperatorMemberMap? member
  | "string" => string.pythonStringMemberMap? member
  | "numpy" => numpy.pythonNumpyMemberMap? member
  | "passta" => passta.pythonPasstaMemberMap? member
  | "random" => random.pythonRandomMemberMap? member
  | "scipy" => scipy.pythonScipyMemberMap? member
  | "pandas" => pandas.pythonPandasMemberMap? member
  | "sortedcontainers" => sortedcontainers.pythonSortedcontainersMemberMap? member
  | _ => none

/-- Proof-mode (`PyProofM`) registry: the `IO`-effectful library members whose pure, state-threaded
twins run in the proof monad. Codegen consults this FIRST when `shouldUseProofMonad` (exact mode), so
`random.randint(...)` lowers to `pyRandomRandintProof` (a `PyProofM Int`) instead of the `IO` version,
which cannot be `←`-bound in the pure proof monad. A miss falls through to the regular map. -/
def pythonLibraryMapProof? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "random" => random.pythonRandomMemberMapProof? member
  | _ => none

/--
Exact-mode (`ℝ`, `noncomputable`) registry for transcendental library members.

In the default numeric mode codegen consults this first; a hit lowers `math.exp` etc. to the
`Real.*`-backed version (provable, not runnable). A miss falls back to `pythonLibraryMap?` (the
regular, often `Float`-valued, mapping) — so non-transcendental members are unaffected.
-/
def pythonLibraryMapReal? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "math" => math.pythonMathMemberMapReal? member
  | "numpy" => numpy.pythonNumpyMemberMapReal? member
  | "scipy" => scipy.pythonScipyMemberMapReal? member
  | _ => none

/-- Exact-mode overrides that are computable + provable but NOT transcendental `ℝ` (e.g.
`math.pow` with an integer exponent → rational power). Consulted in exact mode after the real map
and before the regular (`Float`) map. -/
def pythonLibraryMapExact? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "math" => math.pythonMathMemberMapExact? member
  | "numpy" => numpy.pythonNumpyMemberMapExact? member
  | _ => none

/-- The `Behaviour` of a **qualified** library member `module.member` — the single record carrying
its return shape, mutation, and iterator kind. Adding a library member is one entry in that library's
own `Mapping.lean`; this dispatch and the derived views below never change. -/
def memberBehaviour? (moduleName member : String) : Option Behaviour :=
  match moduleName with
  | "heapq"       => heapq.heapqBehaviour? member
  | "itertools"   => itertools.itertoolsBehaviour? member
  | "collections" => collections.collectionsBehaviour? member
  | "bisect"      => bisect.bisectBehaviour? member
  | "functools"   => functools.functoolsBehaviour? member
  | "hashlib"     => hashlib.hashlibBehaviour? member
  | "json"        => json.jsonBehaviour? member
  | "math"        => math.mathBehaviour? member
  | "scipy"       => scipy.scipyBehaviour? member
  | "numpy"       => numpy.numpyBehaviour? member
  | "sortedcontainers" => sortedcontainers.sortedcontainersBehaviour? member
  | _ => none

/-- The `Behaviour` of a BARE callable name (a builtin, or a star-imported library member) — the entry
point TypeInfer consults for a `Name` call. Excludes `math`/`scipy`/`numpy`, which are qualified-only,
so a user function named `pow`/`sqrt`/`dot` is not shadowed by the library. -/
def bareBehaviour? (name : String) : Option Behaviour :=
  (builtinBehaviour? name).orElse fun _ =>
  (itertools.itertoolsBehaviour? name).orElse fun _ =>
  (heapq.heapqBehaviour? name).orElse fun _ =>
  (collections.collectionsBehaviour? name).orElse fun _ =>
  (functools.functoolsBehaviour? name).orElse fun _ =>
  (bisect.bisectBehaviour? name)

/-! ### Views derived from `memberBehaviour?` — one field each, so existing call sites are unchanged. -/

-- `libraryMemberReturn?` (type-only) moved to `Libraries/TypeBehaviour.lean`, next to the other
-- type-inference aggregators the engine imports.

/-- The in-place mutation spec of a library member, for the core codegen. -/
def libraryMutator? (moduleName member : String) : Option LibraryMutator :=
  (memberBehaviour? moduleName member).bind (·.mutator)

/-- The unbounded-iterator spec of a library member, for the core codegen. -/
def libraryInfiniteIter? (moduleName member : String) : Option InfiniteIter :=
  (memberBehaviour? moduleName member).bind (·.infiniteIter)

/-- Library modules whose members live in `IO` because they read or advance global mutable state
(`random`'s generator). A call to one makes its enclosing function IO-effectful, exactly as
`input()` does. Declared here rather than in the Python driver so a library's facts stay in one
place; the driver reads it over the `libraryInfo` backend task. -/
def ioEffectfulLibraries : List String := ["random"]

/-- A library implemented as classes (`datetime`): its class declarations, as JSON-IR text, for the
driver to inject into an importing program (see `Libraries/datetime/Mapping.lean`). -/
def classLibraryDecls? (moduleName : String) : Option String :=
  match moduleName with
  | "datetime" => some datetime.datetimeClassDecls
  | _ => none

/-- The libraries `classLibraryDecls?` covers, for the driver's `libraryInfo` query. -/
def classLibraries : List String := ["datetime"]

/-- Library members (`module.member`) that can raise a Python exception, so a call to one makes its
enclosing function exception-effectful exactly as a `raise` does. Read by the driver like
`ioEffectfulLibraries`. -/
def raisingLibraryMembers : List String :=
  json.jsonRaisingMembers.map ("json." ++ ·)

/-- Does this member construct a library-owned object (`hashlib.md5()`)? Codegen tags the assigned
variable with the owning module so its methods route through `libraryMethod?`. -/
def libraryObjectConstructor? (moduleName member : String) : Bool :=
  ((memberBehaviour? moduleName member).map (·.constructsObject)).getD false

/-- A METHOD on a library-owned object → its runtime function. Consulted only when the receiver is
a variable known to hold an object of that module, so a name that collides with a builtin method
(`update`) still resolves correctly for ordinary dicts and sets. One entry point, so codegen names
no specific library. -/
def libraryMethod? (moduleName member : String) : Option Lean.Name :=
  match moduleName with
  | "hashlib" => hashlib.hashlibMethod? member
  | _ => none

/-- Does this member wrap a comparator into a sort key (`functools.cmp_to_key`)? Keyed on the member
name alone as well as qualified, since it reaches codegen either way (`from functools import
cmp_to_key` gives a bare name). Lets the core sort lowering unwrap it without naming any library. -/
def isCmpKeyWrapper (member : String) : Bool :=
  ((bareBehaviour? member).map (·.cmpKeyWrapper)).getD false ||
    ((memberBehaviour? "functools" member).map (·.cmpKeyWrapper)).getD false

/-- A method that a library declares as a no-op, for the core codegen — keyed on the method name
alone (these come from decorated values, e.g. `f.cache_clear()`, which carry no module tag). One
entry point, so codegen names no specific library. -/
def libraryNoopMethod? (member : String) : Option Lean.Name :=
  functools.functoolsNoopMethod? member

/-- A `sortedcontainers.SortedList` instance method → its runtime function. Codegen consults this
only when the receiver is a known SortedList (several names collide with set/list/bisect). One entry
point, so codegen names no specific library. -/
def sortedListMethod? (member : String) : Option Lean.Name :=
  sortedcontainers.sortedListMethod? member

/-- A decorator a library declares transparent — no effect on the transpiled value, so the decorated
function is emitted unchanged (e.g. functools' `@cache`). One entry point, so codegen names no
specific library. The caller passes the decorator's last dotted segment (`functools.cache` → `cache`). -/
def libraryTransparentDecorator? (name : String) : Bool :=
  functools.functoolsTransparentDecorator? name

end Libraries
