import VersoSlides
import Verso.Doc.Concrete
import PastaLean
import Libraries
import Std
import Std.Tactic.Do

set_option verso.code.warnLineLength 500
set_option verso.slides.panel false
set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option verso.slides.warnOnImage false

open VersoSlides
open PastaLean Libraries Libraries.numpy Libraries.passta Std.Do

/- A `timeDay` inline role: renders the wall-clock date at the moment this doc is built (elaborated),
e.g. "21 July 2026" — invoke as `{timeDay}`·``. It re-runs whenever this file is recompiled, so a
fresh `lake build` / `lake exe slides` refreshes it. -/
open Verso Doc Elab ArgParse in
open Lean Elab Widget in
open Lean.Doc.Syntax in
@[role]
meta def timeDay : RoleExpanderOf Unit
  | (), _ => do
    let out ← IO.Process.run { cmd := "date", args := #["+%d %B %Y"] }
    let html := Verso.Output.Html.text false out.trimAscii.toString
    ``(Verso.Doc.Inline.other (VersoSlides.InlineExt.ofHtml $(quote html)) #[])

#doc (Slides) "PastaLean" =>

# PastaLean

%%%
state := "title"
%%%

:::class "subheader"
_Transpiling_ and _Verifying_ Python in Lean 4 — without LLMs
:::

:::class "byline"
*Anirudh Gupta* · IISc Bengaluru

*Petros Markopoulos* · UC San Diego

*Swarnava Chakraborty* · IISc Bengaluru

*Siddhartha Gadgil* · Professor · IISc Bengaluru
:::

:::class "timeDay"
{timeDay}`·`
:::

:::class "links"
[GitHub PyAstLean](https://github.com/siddhartha-gadgil/PyAstLean)
:::

# Overview

:::class "steps"
* *Why* verify Python at all — and why in Lean
* *How* PastaLean turns Python into Lean, node by node
* *What* we support: control flow, classes, libraries…
* *Proving* the generated code correct
:::

# What are we cooking?

```html
<div class="eq">
  <span class="term fragment" data-fragment-index="1"><img class="pasta" src="assets/pasta.jpg" alt="pasta"><span class="cap">Pasta</span></span>
  <span class="op fragment" data-fragment-index="2">+</span>
  <span class="term fragment" data-fragment-index="3"><img src="assets/python-clean.png" alt="python"><span class="cap">Python</span></span>
  <span class="op fragment" data-fragment-index="4">+</span>
  <span class="term fragment" data-fragment-index="5"><img src="assets/lean-logo-large.png" alt="lean"><span class="cap">Lean 4</span></span>
  <span class="op fragment" data-fragment-index="6">=</span>
  <span class="result fragment" data-fragment-index="7"><img class="eqlogo" src="assets/pastaleanlogo.png" alt="PastaLean"></span>
</div>
```

::::fragment

:::class "punch"
P·_ast_·aLean  →  *PastaLean*
:::

::::

:::fragment
How to eat(use) PastaLean?
:::

:::class "steps"

* Take ordinary, _logical_ Python — the kind data scientists and practical logical code's LLMs actually write.
* Preprocess Python code for Type annotations, obtain it's Abstract Syntax Tree(AST) and give Lean it's JSON format.
* _Transpile_ it into Lean 4 — deterministically, with no LLM, so the
  meaning never drifts.
* _Prove_ it correct — and let Lean's proof automation do the heavy lifting with a little help by LLM's.
:::

::::fragment
:::class "punch"
The *Goal*: write in Python, get the guarantees of a proof assistant.
:::
::::

# What is the Inspiration for this dish?

:::class "steps"
* Two things dominate how code gets written today: *Python* (the language) and
  *LLMs* (increasingly, the author).
* A huge and growing share of the Python running in the world was drafted by an LLM.
* But here's the uncomfortable question:
:::

::::fragment
:::class "punch"
Who checks that the generated code is actually _correct_?
:::
::::

:::class "steps"
* _Tests only catch the bugs you thought to write — never the ones you didn't._
* To _prove_ correctness (not merely test it), we reach for *formal methods*:
  Hoare logic, model checking, multi-modal verification…
* *Proof assistants* make that practical — and there are several:
  *Lean 4*, Rocq (Coq), Isabelle, Dafny, …
* We use *Lean 4*: a proof assistant that is _also_ a fast, real
  programming language.
:::


# Why Lean?

Lean 4 is a proof assistant _and_ a general-purpose language (it compiles to C — genuinely fast).

```html
<div class="stats">
  <div class="stat">1.9M+<small>lines in Mathlib, its math library</small></div>
  <div class="stat">282k+<small>theorems · 134k definitions</small></div>
  <div class="stat">772<small>contributors · 1 tiny trusted kernel</small></div>
</div>
```

* *Powerful automation* — tactics like `simp`, `grind`,
  `aesop`, etc. search proofs and close goals for you, often in one line.
* *Endlessly customizable* — custom syntax, macros, and tactics let you extend
  the language itself — exactly how PastaLean is built.
* *Trusted where it matters* — used by Fields medallist *Terence Tao*, backed by
  the *Lean FRO*, applied to industrial verification.
* A small, auditable *kernel* re-checks every proof — nothing is taken on faith.


See Leo de Moura's blog [*Why Lean?*](https://leodemoura.github.io/blog/2026-4-2-why-lean/).


# Why convert Python into Lean?

:::fragment
* Blindly trusting an LLM's Python means shipping logic _no one has proved_ —
silent wrong answers, bad edge cases, security holes.
:::

:::fragment
*_PastaLean_ gives that code a home where the compiler is the reviewer:*
:::

:::class "steps"
* if it type-checks against our runtime, the *translation* is faithful;
* if the proof closes, the *logic* is correct.
:::

::::fragment
:::class "punch"
Write it in Python. Trust it like Lean.
:::
::::

:::fragment
And because pure Python becomes bare Lean _terms_, we can state and prove theorems about it.
:::

# Why transpile — and not just ask an LLM?

::::fragment
The obvious shortcut: _"LLM, translate this Python to Lean."_ We deliberately do
_not_ do that for the core translation. LLMs earn their keep elsewhere — proposing _contracts_ — never as the translator.

:::table +colHeaders +rowSeps +border
*
  * *Prompt an LLM to translate*
  * *PastaLean (AST transpiler)*
*
  * Hallucinates; silently changes semantics
  * Deterministic — same node, same Lean, always
*
  * Not reproducible, not auditable
  * One runtime pins _what each operation means_
*
  * Breaks on long / scaled programs
  * Compositional: per-statement, streamed
*
  * No ground truth that it is correct
  * Output is _checked_ by the Lean elaborator
:::

::::

:::fragment

_Other Possible methods maybe?_
:::

::::fragment

:::class "step"
* Other Methods like using FFI is possible, however theorem proving would not be possible.
* Converting Lean to Python is possible, however legacy python checking would not be possible and there are a lot more python programmers.
:::

::::

# How does PastaLean taste code?

%%%
state := "whatis"
%%%

:::fragment

It reads Python's *AST* and emits Lean you can _prove_:
:::

:::::hstack
::::vstack
:::class "gbox" "py" "fragment"
```code python
def sum_to_n(n: int) -> int:
    Requires(n >= 0)
    total = 0
    for i in range(n + 1):
        Invariant(2*total == i*(i - 1))
        total = total + i
    Ensures(2*total == n*(n + 1))
    return total
```
:::

:::class "arrow-down" "fragment"
↓ _ast-parse_
:::

```html
<pre class="ast fragment"><span class="d">FunctionDef</span>(name=<span class="s">'sum_to_n'</span>,
  args=[arg(<span class="s">'n'</span>, Name(<span class="s">'int'</span>))],
  body=[
    Expr(Call(<span class="k">Requires</span>,
      Compare(Name<span class="s">'n'</span>, GtE, <span class="n">0</span>))),
    AnnAssign(<span class="s">'total'</span>, Name<span class="s">'int'</span>, <span class="n">0</span>),
    For(<span class="s">'i'</span>, Call(range, …), body=[
      Expr(Call(<span class="k">Invariant</span>, …)),
      Assign(<span class="s">'total'</span>, BinOp(…, Add, …))]),
    Expr(Call(<span class="k">Ensures</span>, …)),
    Return(Name<span class="s">'total'</span>)])</pre>
```
::::

:::class "arrow-right" "fragment"
→ _transpile_
:::

::::vstack
:::class "gbox" "defbox" "fragment"
```lean
def sum_to_n := fun (n : Int) ↦
  (do
    let mut total := (0 : Int)
    for i in (PastaLean.pyRange (n +ₚ (1 : Int)))do
      let _ := Libraries.passta.pyPassInvariant ((2 : Int) *ₚ total == i *ₚ (i -ₚ (1 : Int)))
      total := total +ₚ i
    let _ := Libraries.passta.pyPassEnsures ((2 : Int) *ₚ total == n *ₚ (n +ₚ (1 : Int)))
    return total : Id _)
```
:::

:::class "arrow-down" "prove-arrow" "fragment"
↓ _prove — automatically_
:::

:::class "gbox" "thm" "fragment"
```lean
theorem sum_to_n_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ sum_to_n n ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [sum_to_n, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, total⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      (2 : Int) *ₚ total = i *ₚ (i -ₚ (1 : Int))⌝
  simp_all [taste_ingr]; grind +locals +suggestions
```
:::
::::
:::::


:::class "gbox" "fragment"
```lean
#eval sum_to_n 10
```
:::


# Two Functions for each code

%%%
state := "twofns"
vertical := some true
%%%

::::fragment
PastaLean converts each function in Python into 2 functions each with it's own purpose:

:::class "step"
- *Provable* - This function is meant to be used for property proving of the function.
- *Computable* - This function is meant to be computable with `#eval`. These are marked with `'rn` in function name, which stands for `run`.
:::
::::

::::fragment

:::table +colHeaders +rowSeps +border
*
  * *Difference*
  * *Provable*
  * *Computable*
*
  * Python `float`
  * Converted to {lean}`ℚ` or {lean}`ℝ`(if transcendental functions are used).
  * Lean's inbuilt {lean}`Float` is always used.
*
  * Provable
  * Yes
  * Sometimes depending on function, not always.
*
  * Computable
  * Sometimes. If ℝ is used then never.
  * Yes
*
  * API differences(`print`, `exceptional-handling`)
  * Special non-IO Monad based functions are used to support proving.
  * IO Monad functions are used for real behaviour.

:::
::::

# Example of Provable/Computable Function

%%%
state := "examples"
%%%

:::fragment
One Python function forks into two Lean definitions:
:::

::::::vstack
:::class "pytop" "fragment"
```code python
def euclidean_distance(p1, p2):
    if len(p1) != len(p2):
        raise ValueError("Points must have the same number of dimensions")

    # Using zip, list comprehension, and math.pow
    sq_diffs = [math.pow(a - b, 2) for a, b in zip(p1, p2)]
    return math.sqrt(sum(sq_diffs))
```
:::

:::::hstack
::::vstack
:::class "arrow-dl" "fragment"
↙ _provable_
:::

:::class "gbox" "prov" "fragment"
```lean
noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  ((do
      if h_1 : PastaLean.pyLen p1 ≠ PastaLean.pyLen p2 then
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString "Points must have the same number of dimensions"))
      else
        let _ := ()
      -- Using zip, list comprehension, and math.pow
      let mut sq_diffs :=
        (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
          let a := Prod.fst _pair_1;
          let b := Prod.snd _pair_1;
          Libraries.math.pyMathPowExact (a -ₚ b) (2 : Int)
      let __py_ret_1 := Libraries.math.pyMathSqrtR (PastaLean.pySum sq_diffs)
      return __py_ret_1) :
    PastaLean.PyExceptId _)
```
:::
::::

::::vstack
:::class "arrow-dr" "fragment"
↘ _computable_
:::

:::class "gbox" "comp" "fragment"
```lean

def euclidean_distance'rn : List Int → List Int → PastaLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if h_1 : PastaLean.pyLen p1 != PastaLean.pyLen p2 then
    throw
        (PastaLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
      let a := Prod.fst _pair_1;
      let b := Prod.snd _pair_1;
      Libraries.math.pyMathPow (a -ₚ b) (2 : Int)
  let __py_ret_1 := Libraries.math.pyMathSqrt (PastaLean.pySum sq_diffs)
  return __py_ret_1
```
:::
::::
:::::
::::::


# How much Python is convertable?

%%%
state := "implemented"
vertical := some true
%%%

:::fragment
Most everyday Python is convertable into Lean4. Extending new Python syntax is made very trivial with the help of our underlying design architecture.
:::

::::fragment

:::table +colHeaders +rowSeps +border
*
  * Area
  * Python constructs handled
*
  * Control flow
  * `if / elif / else`, `for`, `while`, `break`, `continue`, `match`
*
  * Functions
  * `def`, `lambda`, `return`, default args, nested defs
*
  * Data structures
  * `list`, `dict`, `set`, `tuple`, slicing, `x[i]`, `x[i] = v`
*
  * Comprehensions
  * list / dict / set / generator comprehensions
*
  * Exceptions
  * `try` / `except` / `finally`, `raise`, `assert`
*
  * OOP
  * `class`, methods, `self`, fields, dunder methods, inheritance
*
  * Strings & misc
  * f-strings, `import` / `from … import`, `del`, augmented assign
:::
::::

:::fragment
and more...
_↓ press down to see the constructs by area, with examples._
:::

## Control flow

%%%
state := "cflow"
%%%

*Branches & recursion*

::::hstack
:::class "excode" "fragment"
```code python
def fibonacci(n: int):
    if n <= 0:
        return 0
    elif n == 1:
        return 1
    else:
        return fibonacci(n - 1) + fibonacci(n - 2)
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
partial def fibonacci : Int → Int := fun (n : Int) ↦
  if decide (n ≤ (0 : Int)) then (0 : Int)
  else if n == (1 : Int) then (1 : Int)
  else fibonacci (n -ₚ (1 : Int)) +ₚ fibonacci (n -ₚ (2 : Int))
```
:::
::::

*Loops & mutation* → an `Id.run do` block:

::::hstack
:::class "excode" "fragment"
```code python
def classify(nums: list[int]):
    total = 0
    for n in nums:
        if n % 2 == 0:
            total += n
        else:
            total -= n
    return total
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
def classify := fun (nums : List Int) ↦
  Id.run
    (do
      let mut total := (0 : Int)
      for n in (PastaLean.pyIter nums)do
        if h_1 : n %ₚ (2 : Int) = (0 : Int) then
          total := total +ₚ n
        else
          total := total -ₚ n
      return total)
```
:::
::::

:::fragment
Statements outside functions(in open) are also well supported.
:::

## Data structures & comprehensions

%%%
state := "datastruct"
%%%

`list` · `dict` · `set` · `tuple`, slicing, indexing, container methods:

*Comprehensions* → `map` / `filter`

::::hstack
:::class "excode" "fragment"
```code python
squares = [x*x for x in range(10)
               if x % 2 == 0]

cubes = {n: n**3 for n in range(5)}

evens = {x for x in range(10)
             if x % 2 == 0}
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
def squares :=
  (List.filter (fun x => x %ₚ (2 : Int) == (0 : Int))
    (PastaLean.pyRange (10 : Int))).map fun x => x *ₚ x

def cubes :=
  Std.HashMap.ofList
    ((PastaLean.pyRange (5 : Int)).map fun n => (n, n ^ₚ (3 : Int)))

def evens :=
  PastaLean.pySetFromList
    ((List.filter (fun x => x %ₚ (2 : Int) == (0 : Int))
      (PastaLean.pyRange (10 : Int))).map fun x => x)
```
:::
::::

*List & string ops*

::::hstack
:::class "excode" "fragment"
```code python
nums = [3, 1, 2, 4]
head = nums[0]         # index
tail = nums[1:]        # slice
size = len(nums)

s = "hello world"
words = s.split(" ")
loud = s.upper()
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
def nums := [(3 : Int), (1 : Int), (2 : Int), (4 : Int)]
def head := nums⦋(0 : Int)⦌
def tail := PastaLean.pySlice nums (some (1 : Int)) none none
def size := PastaLean.pyLen nums

def s := "hello world"
def words := PastaLean.pyStringSplit s " "
def loud := PastaLean.pyStringUpper s
```
:::
::::

:::class "punch" "fragment"
`x[i]` → {name}`pyGetItem`,  slicing → {name}`pySlice`,  `iter` → {name}`pyIter`
:::

## Exception handling

%%%
state := "exc"
%%%

`try` / `except` / `finally`, `raise`, typed `except ValueError as e` — one function, two twins:

::::::vstack
:::class "pymid" "fragment"
```code python
def divide_add(a, b, c):
    try:
        result = a / b
        while result < c:
            result += 1
        return result
    except ZeroDivisionError:
        return "Division by zero error"
    finally:
        print("PastaLean handles exceptions gracefully.")
```
:::

:::::hstack
::::vstack
:::class "arrow-dl" "fragment"
↙ _provable_
:::

:::class "excode" "prov" "fragment"
```lean
def divide_add := fun a ↦ fun b ↦ fun c ↦
  ((do
      try
        let mut result := a /ₚ b
        while (result < c) do
          result := result +ₚ (1 : Int)
        return result
      catch caught =>
        if (caught).OfKind == "ZeroDivisionError" then
          let _ ← pyPrintNoop [pyPrintArg "Division by zero error"]
          let __py_ret_1 := -(1 : Int)
          return __py_ret_1
        else
          throw caught
      finally
        do
          let _ ← pyPrintNoop [pyPrintArg "PastaLean handles exceptions gracefully."]) :
    PastaLean.PyExceptId _)
```
:::
::::

::::vstack
:::class "arrow-dr" "fragment"
↘ _computable_
:::

:::class "excode" "comp" "fragment"
```lean
def divide_add'rn := fun a ↦ fun b ↦ fun c ↦
  ((do
      try
        let mut result := a /ₚ b
        while (result < c) do
          result := result +ₚ (1 : Int)
        return result
      catch caught =>
        if (caught).OfKind == "ZeroDivisionError" then
          let _ ← pyPrintIO [pyPrintArg "Division by zero error"]
          let __py_ret_1 := -(1 : Int)
          return __py_ret_1
        else
          throw caught
      finally
        do
          let _ ← pyPrintIO [pyPrintArg "PastaLean handles exceptions gracefully."]) :
    PastaLean.PyExcept _)
```
:::
::::
:::::
::::::

:::class "punch" "fragment"
{lean}`PyExceptId` (pure, provable) vs {lean}`PyExcept` = {lean}`ExceptT PyException IO` (real {lean}`IO`).
:::

# Classes / OOP

A Python `class` becomes a Lean `structure` plus namespaced method definitions. `self`
is the structure value, and mutation is value-semantics (`C.new` builds one):

:::hstack
```code python
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def norm_sq(self):
        return self.x*self.x \
             + self.y*self.y

obj = Point(1,2)
norm = obj.norm_sq()
```

```lean
structure Point where
  x : Int
  y : Int
  deriving Inhabited, Repr, BEq

def Point.new := fun x ↦ fun y ↦ ({ x := x, y := y } : Point)
def Point.norm_sq := fun (self : Point) ↦ self.x *ₚ self.x +ₚ self.y *ₚ self.y

def obj := Point.new (1 : Int) (2 : Int)
def norm := Point.norm_sq obj
```
:::

:::class "gbox" "fragment"
```lean
#check obj
#eval norm
```
:::
# Libraries

:::fragment
Implementing Library and integrating it in PastaLean is very trivial.
:::

::::fragment
:::class "step"
- All you do is write the Lean function for your Python implementation, use our builtin typeclasses support if needed. All Libraries are independently implementable.
- Now just map the member name to a Lean runtime function. This will automatically integrate with our code generation pipeline.
- `numpy`, `pandas`, `scipy`, `math`, `typing` ship today; anything unsupported degrades to a flagged {name}`pyUnsupported` so the file still compiles.
:::
::::

:::fragment
A slice of `numpy`:
:::

::::::hstack
:::::fragment
::::vstack

```lean
open Libraries.numpy in
example : String → Lean.Name := fun member =>
  match member with
  | "array"    => ``pyNumpyArray
  | "dot"      => ``pyNumpyDot
  | "mean"     => ``pyNumpyMean
  | "std"      => ``pyNumpyStd
  | "linspace" => ``pyNumpyLinspace
  | "norm"     => ``pyNumpyNorm
  | _          => .anonymous
```
::::
:::::

::::fragment
:::class "arrow-right" "fragment"
→ _transpile_
:::
::::

:::::fragment
::::vstack

:::fragment
where {name}`pyNumpyNorm` and other functions are as simple as:
:::

:::fragment

```lean
def pyNumpyNorm {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := xs.map toFloat
  Float.sqrt (ys.foldl (fun acc x => acc + x * x) 0.0)
```
:::
::::
:::::
::::::

# Achievements

Transpiled, compiled, and *run* across two full benchmarks — the Lean twin's answers matched against the reference test cases.

*LeetCode* — all *2,589* problems:

```html
<div class="stats">
  <div class="stat">&gt;92%<small>2,391 problems compile</small></div>
  <div class="stat">&gt;97%<small>test cases pass</small></div>
</div>
```

*HumanEval+* — all *164* problems:

```html
<div class="stats">
  <div class="stat">92.1%<small>151 / 164 compile</small></div>
  <div class="stat">100%<small>test cases pass · 7,007 / 7,007</small></div>
</div>
```

# Showcases

%%%
state := "showcase"
vertical := some true
%%%

Real programs — _transpiled_, _type-checked_, and (for the pure parts) _proved_. Full code on [_GitHub_](https://github.com/AnirudhG07/PyAstLean/tree/master/example_scripts/showcase).

```html
<div class="stats">
  <div class="stat">6<small>real programs</small></div>
  <div class="stat">~560<small>lines of Python</small></div>
  <div class="stat">~1,330<small>lines of verified Lean</small></div>
  <div class="stat">&lt; 8s<small>each · type-check + prove</small></div>
</div>
```

:::table +colHeaders +rowSeps +border
*
  * Showcase
  * Python
  * → Lean
  * Checks in
  * Exercises
*
  * `eg1`
  * 39 loc
  * 148 loc
  * 5.2 s
  * exceptions · `zip` · comprehensions · `math`
*
  * `eg2`
  * 36 loc
  * 97 loc
  * 5.1 s
  * `numpy` mean · matmul · `try`/`except`
*
  * `orbital`
  * 186 loc
  * 386 loc
  * 7.8 s
  * vector algebra · conserved quantities · _proved_
*
  * `cnn`
  * 141 loc
  * 355 loc
  * 5.4 s
  * a from-scratch CNN class · forward + backprop
*
  * `nn`
  * 51 loc
  * 134 loc
  * 5.2 s
  * a neural-net forward pass
*
  * `linalg`
  * 107 loc
  * 208 loc
  * 5.9 s
  * 2×2 matrix algebra · all _proved_
:::

:::class "punch" "fragment"
~560 lines of Python → ~1,330 lines of _verified_ Lean — every one type-checked, the pure parts _proved_, all in seconds.
:::

:::fragment
_↓ press down to walk through three of our showcases._
:::

## Orbital Physics · conserved quantities

:::fragment
_Vector algebra where the Python `assert`s — conserved momentum, a central spring force — become *theorems*, closed automatically._
:::

::::hstack
:::class "showpy" "fragment"
```code python

def cross_x(ax: float, ay: float, az: float, bx: float, by: float, bz: float) -> float:
    """x-component of a x b."""
    return ay * bz - az * by

def norm_sq(ax, ay, az):
    return ax*ax + ay*ay + az*az

def kinetic(m, vx, vy, vz):
    return 0.5 * m * norm_sq(vx, vy, vz)

def momentum(m, vx, vy, vz):
    return m * norm_sq(vx, vy, vz)

def spring_energy(k: float, dx: float, dy: float, dz: float) -> float:
    """Hooke potential energy (1/2) k |d|^2 stored in a spring stretched by displacement d."""
    return 0.5 * k * norm_sq(dx, dy, dz)

def momentum_conserved(m1: float, v1: float, m2: float, v2: float, j: float):
    """Equal and opposite impulses +j / -j conserve total linear momentum (1-D component)."""
    assert (m1 * v1 + j) + (m2 * v2 - j) == m1 * v1 + m2 * v2

def spring_force_is_central(k: float, dx: float, dy: float, dz: float):
    """The Hooke force F = -k d is central (anti-parallel to the displacement d), so it too exerts
    no torque about the spring axis: d x F = 0 (x-component)."""
    assert cross_x(dx, dy, dz, -k * dx, -k * dy, -k * dz) == 0

```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "showlean" "fragment"
```lean
def cross_x := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun (cy : Rat) ↦ fun (bz : Rat) ↦
  ay *ₚ bz -ₚ az *ₚ cy

def norm_sq := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ ax *ₚ ax +ₚ ay *ₚ ay +ₚ az *ₚ az

def kinetic := fun (m : Rat) ↦ fun (vx : Rat) ↦ fun (vy : Rat) ↦ fun (vz : Rat) ↦ (0.5 : Rat) *ₚ m *ₚ norm_sq vx vy vz

def momentum := fun (m : Rat) ↦ fun (vx : Rat) ↦ fun (vy : Rat) ↦ fun (vz : Rat) ↦ m *ₚ norm_sq vx vy vz

def spring_energy := fun (k : Rat) ↦ fun (dx : Rat) ↦ fun (dy : Rat) ↦ fun (dz : Rat) ↦
  /-
  Hooke potential energy (1/2) k |d|^2 stored in a spring stretched by displacement d.
  -/
  (0.5 : Rat) *ₚ k *ₚ norm_sq dx dy dz

@[taste_ingr]
theorem momentum_conserved :
    ∀ (m1 : Rat),
      ∀ (v1 : Rat), ∀ (m2 : Rat), ∀ (v2 : Rat), ∀ (j : Rat), m1 *ₚ v1 +ₚ j +ₚ (m2 *ₚ v2 -ₚ j) = m1 *ₚ v1 +ₚ m2 *ₚ v2 :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]

@[taste_ingr]
theorem spring_force_is_central :
    ∀ (k : Rat),
      ∀ (dx : Rat), ∀ (dy : Rat), ∀ (dz : Rat), cross_x dx dy dz (-k *ₚ dx) (-k *ₚ dy) (-k *ₚ dz) = (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; grind +locals

```
:::
::::

## cnn · a CNN, transpiled

:::fragment
_A from-scratch convolution — nested loops, `self.kernel`, value-semantics mutation — transpiled verbatim._
:::

::::hstack
:::class "showpy" "fragment"
```code python
class CNN:
    def conv(self, img):
        # valid 2x2 conv: 8x8 → 7x7
        out = []
        for i in range(7):
            row = []
            for j in range(7):
                s = 0.0
                for a in range(2):
                    for b in range(2):
                        s += img[i+a][j+b] \
                           * self.kernel[a][b]
                row.append(s)
            out.append(row)
        return out
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "showlean" "fragment"
```lean
structure CNN where
  kernel : List (List Real)
  dense_w : List Real
  dense_b : Real
  deriving Inhabited

noncomputable def CNN.conv := fun (self : CNN) ↦ fun (img : List (List Rat)) ↦
  Id.run
    (do
      let mut out := []
      for i in (PastaLean.pyRange (7 : Int))do
        let mut row := []
        for j in (PastaLean.pyRange (7 : Int))do
          let mut s := (0.0 : Real)
          for a in (PastaLean.pyRange (2 : Int))do
            for b in (PastaLean.pyRange (2 : Int))do
              s := s +ₚ img⦋i +ₚ a⦌⦋j +ₚ b⦌ *ₚ self.kernel⦋a⦌⦋b⦌
          row := PastaLean.pyAppend row s
        out := PastaLean.pyAppend out row
      return out)
```
:::
::::

## numpy + exceptions

:::fragment
_`np.mean` and `matmul` inside `try`/`except` — a library call, real control flow, both twins._
:::

::::vstack
:::class "showpy" "fragment"
```code python
def process_data(data, weights):
    try:
        m = np.mean(data)
        print(f"Mean: {m}")
        centered = np.subtract(data,
                       [[m, m], [m, m]])
        return np.matmul(centered, weights)
    except ValueError as e:
        print(f"Failed: {e}")
        return np.zeros((2, 2))
```
:::

:::class "arrow-down" "fragment"
↓
:::

:::class "showlean" "fragment"
```lean
def process_data := fun (data : List (List Rat)) ↦ fun (weights : List (List Rat)) ↦
  ((do
      try
        let mut m := Libraries.numpy.pyNumpyMean data
        let _ ← pyPrintNoop [pyPrintArg s! "Mean: {m}"]
        let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
        let mut result := Libraries.numpy.pyNumpyMatmul centered weights
        return result
      catch caught =>
        if (caught).OfKind == "ValueError" then
          let e := caught
          let _ ← pyPrintNoop [pyPrintArg s! "Failed: {e}"]
          let __py_ret_1 := Libraries.numpy.pyNumpyZeros ((2 : Int), (2 : Int))
          return __py_ret_1
        else
          throw caught) :
    PastaLean.PyExceptId _)
```
:::
::::

# Design & architecture

%%%
state := "design"
vertical := some true
%%%

:::class "dhook"
The choices that make a _faithful_, _provable_ translation possible — press ↓.
:::

:::class "steps"
* *Problem → What we did → Why*, one architectural decision at a time.
* Pure architecture — the elaborator and instance resolution do the heavy lifting.
:::

## 1 · The logic subset

:::class "dhook"
Not all of Python is supported, however, efforts into supporting the _provable_ subset are made.
:::

:::class "steps"
* *Problem* — Python is dynamic: `eval`, `yield`, monkey-patching — no single static meaning.
* *We do* — target the typed "logic" subset; anything else degrades to a flagged {name}`pyUnsupported`.
:::

:::class "dcode" "fragment"
```code python
# in scope — a static, provable core
xs: list[int] = [1, 2, 3]
total = sum(x * x for x in xs)

# out of scope → `pyUnsupported`, flagged
async def fetch(): await conn.read()   # async
result = eval(user_input)              # reflection
def gen(): yield 1                     # laziness
```
:::

## 2 · One name, many types

:::class "dhook"
`len(x)` is _one_ Lean call — the type system picks the implementation.
:::

:::class "steps"
* *Problem* — `len`, `x[i]`, `x in y`, `x+y` work on many types; codegen often can't _see_ the type yet.
* *We do* — emit one stable name; Lean's _instance resolution_ (after elaboration) selects the impl.
* *Why* — codegen stays type-blind; a new container = one new instance, _zero_ codegen change.
:::

:::class "dcode" "fragment"
```lean
-- one Lean name; instance resolution picks the impl per type:
#check @pyLen

example : Int := pyLen [1, 2, 3]                      -- List
example : Int := pyLen "hello"                        -- String
example : Int := pyLen (Std.HashMap.ofList [(1, 2)])  -- dict
```
:::

## 3 · Operators via `outParam`

:::class "dhook"
`1 + 2.0 : Float` falls straight out of instance resolution.
:::

:::class "steps"
* *Problem* — Python mixes numeric types (`int+float`, `int+Rat`); Lean's `HAdd` has no widening instances.
* *We do* — custom `+ₚ -ₚ *ₚ` over `PyHAdd α β γ`, the _result_ `γ` an `outParam`.
* *Why* — the result type _reduces_ to a concrete type, so a later `pyLen`/print/index can resolve. (`Rat` defaults stay off — subtle, load-bearing.)
:::

:::class "dcode" "fragment"
```lean
#check @PyHAdd

-- the result type is COMPUTED from the operands (the outParam γ):
example : Int    := (1 : Int) +ₚ (2 : Int)
example : Float  := (1 : Int) +ₚ (2.0 : Float)
example : String := "a" +ₚ "b"
```
:::

## 4 · Classes are values

:::class "dhook"
`self.x = 5` — on an _immutable_ Lean structure.
:::

:::class "steps"
* *Problem* — Python objects mutate in place; Lean structures are immutable values.
* *We do* — mutation = _rebuild-and-return_; the receiver is reassigned at the call site.
* *Why* — classes stay _pure & provable_ (no heap / `IORef` monad). Cost: no aliasing — surfaced as an error, never a silent bug.
:::

:::class "dcode" "fragment"
```lean
-- `self.n = self.n + 1` ↦ record update, rebuilt & returned:
structure Counter where
  n : Int
  deriving Inhabited, Repr, BEq

def Counter.new : Int → Counter := fun (start : Int) ↦
  ({ n := start } : Counter)

def Counter.bump := fun (self : Counter) ↦
  Id.run
    (do
      let mut self := self
      self := { self with n := self.n +ₚ (1 : Int) }
      return self)
```
:::

## 5 · Numbers: exact by default

:::class "dhook"
Python `float` is lossy — a proof can't trust `0.1 + 0.2`.
:::

:::class "steps"
* *Problem* — Python `float` is IEEE-lossy; `0.1 + 0.2 ≠ 0.3`, so a proof can't rely on it.
* *We do* — `float` defaults to exact `ℚ` (provable); `--approx` → Lean `Float`; transcendentals → noncomputable `ℝ`.
* *Why* — exact rationals are decidable and _provable_; you opt into `Float` only when raw speed beats proof.
:::

:::class "dcode" "fragment"
```lean
-- Python floats default to EXACT rationals (ℚ):
example : (1 / 10 + 2 / 10 : Rat) = 3 / 10 := by
  native_decide

-- --approx picks Lean Float; transcendentals → ℝ:
#check (Float.sqrt 2.0)
#check (Real.sqrt 2)
```
:::

## 6 · Built to extend

:::class "dhook"
New syntax, new library, new container — each is a _local, additive_ change.
:::

:::class "steps"
* *Problem* — normally, adding syntax or a library means touching the whole pipeline.
* *We do* — four open extension points: a `@[pygen]` registry, a name→name table, per-library `Mapping.lean`, `outParam` protocol instances.
* *Why* — codegen, IR, and backend never change; the elaborator + instance resolution absorb the variation — new features stay cheap.
:::

:::class "dcode" "fragment"
```lean
-- every extension point produces a real runtime name:
#check @pyLen                        -- a container protocol
#check @pyAppend                     -- a list method
#check @Libraries.numpy.pyNumpyMean  -- a library member
```
:::

## 7 · Nested functions: lambda lifting

:::class "dhook"
A nested `def` reads its parent's locals — you can't just move it to the top level.
:::

:::class "steps"
* *Problem* — `def score(x): return x*w` inside `outer` closes over `w`; `w` _feels_ global to `score` but belongs to `outer`. Lift the `def` naïvely and `w` is lost.
* *We do* — *lambda lifting*: every captured variable (`reads ∩ outer's binders`) becomes an _extra parameter_, passed at each call site. Genuine globals/builtins fall outside the intersection, untouched.
* *Why* — the helper lifts to a sibling `private partial def`, so `outer` stays a plain _provable_ `def` (not `partial`). Mutated captures (`nonlocal`) are _threaded_: parameter in, value out.
:::

:::class "dcode" "fragment"
```lean
-- `def score(x): return x * w`  (w free) ↦ sibling def, w lifted to a parameter:
private def _demo_score := fun (x : Int) ↦ fun (w : Int) ↦ x *ₚ w

def demoOuter := fun (xs : List Int) (w : Int) ↦
  xs.map (fun (x : Int) ↦ _demo_score x w)   -- w supplied at the call site

#eval demoOuter [1, 2, 3] 10                  -- [10, 20, 30]
```
:::

# A major Problem: Python is dynamically typed

%%%
state := "dynprob"
%%%

:::class "steps"
* In Python a *name has no fixed type* — it is just a label on a value, and the type is checked only at _runtime_.
* One function serves _every_ type (duck typing), and a variable can even _change_ type mid-body.
:::

::::hstack
:::class "excode" "fragment"
```code python
# one function, many types
def add(a, b):
    return a + b

add(1, 2)          # 3
add("Hi", "!")     # "Hi!"

# one name, two types
x = 1              # int
x = "hello"        # now str
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "step" "fragment"
* *Lean is statically typed* — every binder needs _one_ type, fixed _before_ the body runs.
* `def add (a : ?) (b : ?)` — which type? `Int`? `String`? both?
* `let mut x : Int` _cannot_ later hold a `String`.
:::
::::

::::fragment
:::class "steps"
* *Native Lean can't paper over it* — you'd write an explicit, _closed_ union `Int ⊕ String ⊕ …` and pattern-match at every single use.
* Python code _never declares that union_ — and it spreads _virally_ through every caller and return.
* Worse. Even `len(x)`, `x[i]`, `+` need a _concrete_ type for instance resolution; a bare "any" leaves them *stuck*.
:::
::::

# …and Python ignores its own type hints

:::class "steps"
* Moreover, Python allows multiple return Types from a function!
* Python doesn't even follow it's own type hints, so we can only rely on them with a pinch of salt.
:::

::::hstack
:::class "excode" "fragment"
```code python
# one function, many types
def add(a: int, b: int) -> int:
    return a + b

add("Hi", "!")  # This works!
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "step" "fragment"
* *Lean is statically typed* — every binder needs _one_ type, fixed _before_ the body runs.
* How do we *Solve*? this big issue?
:::
::::

:::class "punch" "fragment"
We need Python's dynamism _without_ poisoning everything with unions.
:::


# {name}`PyAny` — opening the door to dynamic typing

%%%
state := "pyany"
vertical := some true
%%%

:::class "steps"
* {lean}`PyAny` is a total fallback type inspired from Gradual Typing: infer a concrete Lean type wherever we can, and box _only_ the slots we genuinely can't pin.
* *Why* — one definition then runs at every type; `+ₚ` dispatches on the runtime tag.
* *Assumption* - Any type hints given to Python, are correct. Misuse of type hints i.e. wrong input type(which may work in Python), will be flagged as an error in Lean.
:::

::::hstack
:::class "excode" "fragment"
```code python
# no types given → one def, every type
def add(a, b):
    return a + b
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
-- un-inferred params box to PyAny:
def add := fun (a : PyAny) ↦
          fun (b : PyAny) ↦ a +ₚ b
```
:::
::::

:::class "punch" "fragment"
{lean}`PyAny` is a tagged union; `+ₚ` inspects both tags and delegates.
:::

:::class "steps"
* PastaLean also has it's own *Type Inference engine*, which infers the types of the variables and functions, and boxes them to {lean}`PyAny` only when it is necessary.
:::

:::fragment
_More below ↓_
:::

## Type Mutations and Multiple Return Types

If two branches of a function return different types, the function is boxed to {lean}`PyAny`.

::::hstack
:::class "excode" "fragment"
```code python
# branches disagree → PyAny
def classify(n):
    if n > 0:
        return "positive"   # str
    return 0                # int
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
def classify_num := fun (n : Int) ↦
  (if decide (n > 0) then "positive"
   else (0 : Int) : PyAny)
```
:::
::::

:::fragment
If a variable is reassigned types, then it can be inferred to be of type {lean}`PyAny`:
:::

::::hstack
:::class "excode" "fragment"
```code python
def reassigned():
    x = 1
    x = x + 5          # int arithmetic
    x = "hi"           # now a string
    x = x + "world"    # string concatenation on the new type
    return x
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"
```lean
def reassigned :=
  (let x := (1 : Int)
   let x := x +ₚ (5 : Int)
   let x := "hi"
   let x := x +ₚ "!"
   x : PyAny)
```
:::
::::

:::class "steps"
* By default, only one return Type is allowed in a function, but if two branches of a function return different types, the function is boxed to {lean}`PyAny`.
* Useful for Exceptional Handling, where you may return a value in `try` case, but an error/string in `except` case.
:::

## Computation · dispatch on the tag

At runtime the box carries its type; `+ₚ` (`PyAny.add`) unwraps it, runs the real operation, and re-boxes into {lean}`PyAny`:

:::class "gbox" "fragment"
```lean
#eval add 3 4          -- int   + int   → int
#eval add "x" "y"      -- str   ++ str  → str

-- In python, `True + True = 2`
#eval add true true     -- bool  + bool  → int
```
:::

:::class "punch" "fragment"
A genuine mismatch (`1 + "a"`) folds to `none` — total, never a crash.
:::

# Limitations — where the line is

Honest about what PastaLean does _not_ do:

:::class "steps"
* *Not all of Python* — only the static "logic" subset; no `async`, `yield`, `eval`, or monkey-patching.
* *Proofs aren't free* — `taste?` / `mvcgen` are _best-effort_ automation; hard goals still need a manual proof.
* *Libraries are hand-written* — a new library's functions are implemented + mapped once, then reused everywhere.
* *Unsupported → {lean}`pyUnsupported`* — anything out of scope degrades to a flagged placeholder, so the rest of the file _still compiles_.
:::

:::class "punch" "fragment"
When we can't translate faithfully, we refuse _loudly_ — never miscompile.
:::

# Proving we cooked correctly

%%%
state := "proving"
%%%

:::fragment
*Is it correct?* The proof path forks on one thing — a bare _term_ or a `do` block:
:::

::::::vstack
:::::hstack
::::vstack
:::class "arrow-dl" "fragment"
↙ *Non-Monadic*
:::

:::class "gbox" "fragment"
```lean
def transform_and_cube := fun a ↦ fun b ↦
  let c := a +ₚ b
  let d := a -ₚ b
  let e := c *ₚ d
  e ^ₚ (3 : Int)
```
:::

:::fragment
* *Proves* — equalities, identities
* *Tactics* — `taste?` → `ring` · `grind` · `nlinarith`
* *When* — pure terms, no effects
* Best-Effort use of `taste?`
:::
::::

::::vstack
:::class "arrow-dr" "fragment"
↘ *Monadic verification*
:::

:::class "gbox" "fragment"
```lean
def total (xs : List Int) : Int :=
  Id.run do
    let mut s := 0
    for x in xs do
      s := s +ₚ x
    return s
```
:::

:::fragment
* *Proves* — Hoare triples `⦃P⦄ prog ⦃Q⦄`
* *Tactics* — `mvcgen` · `taste?`
* *When* — loops · mutation · `raise` / {lean}`IO`
* Uses LLM's for contracts, `mvcgen` is feed Loop invariants and subgoals are proven(best-effort) with `taste?`
:::
::::
:::::
::::::

:::class "punch" "fragment"
A preference to Non-monadic pure functional code is given while converting. However it will be lowered to Monadic code with `do`, when necessary.
:::

# Why lower into a monad at all?

:::fragment
Pure functions are total and side-effect free, so they cannot directly express
state updates, early exits, or external effects like IO. Lowering into a monad
gives these behaviors a precise semantic model while keeping the code
composable and type-safe.
:::

:::class "steps"
* `print` / `input` → *`IO`*
* `raise` / `try` / `except` → *`PyExcept`* = `ExceptT PyException IO`
* loops / mutation → *`Id.run do`* (pure, but still a `do` block)
:::

:::class "punch" "fragment"
*Tradeoff* : Extensibility _vs_ Harder to Prove
:::

# The one place an LLM helps: contracts

%%%
state := "contracts"
%%%

:::class "punch" "fragment"
How do we even say what we want to prove?
:::

:::class "steps"
* Annotate Python with _contracts_ — `Requires`, `Ensures`, `Invariant`, `Decreases`, or a plain `assert`.
* PastaLean extracts them as *preconditions*, *postconditions*, and per-loop obligations.
* The *LLM proposes* the contracts; `mvcgen` + `taste?` discharge the _proof_.
:::

:::::hstack
::::vstack
:::class "caplabel" "fragment"
*Before* · Python + contracts
:::

:::class "excode" "fragment"
```code python
def factorial(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() >= 1)
    result, i = 1, 1
    while i <= n:
        Invariant(i >= 1)
        Invariant(n - i + 1 >= 0)
        Invariant(result >= 1)
        Decreases(n - i + 1)
        result = result * i
        i = i + 1
    return result
```
:::
::::

:::class "arrow-right" "fragment"
→ _contracts_
:::

::::vstack
:::class "caplabel" "fragment"
*After* · transpiled Lean
:::

:::class "excode" "fragment"
```lean
def factorial := fun (n : Int) ↦
  (do
    let mut result := (1 : Int)
    for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
      let _ := Libraries.passta.pyPassInvariant (decide (i ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassInvariant (decide (n -ₚ i +ₚ (1 : Int) ≥ (0 : Int)))
      let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassDecreases (n -ₚ i +ₚ (1 : Int))
      result := result *ₚ i
    return result : Id _)
```
:::
::::
:::::


# Best Effort Automatic Proving with `taste?`

%%%
state := "provetaste"
%%%

:::fragment

A Python `assert` on a pure function becomes `theorem … := by taste?` — the _Pastafolio_ engine searches (`simp` · `grind` · `ring` · `nlinarith` · `fun_induction`) and _splices the found proof back_:
:::

::::hstack
:::class "excode" "fragment"
```code python
# showcase/linalg/matrix_model.py
def det(a, b, c, d):
    return a*d - b*c

# scaling a 2×2 by k scales det by k²
assert det(k*a, k*b, k*c, k*d) \
    == k**2 * det(a, b, c, d)
```
:::

:::class "arrow-right" "fragment"
→ _prove_
:::

:::class "excode" "fragment"
```lean
def det (a b c d : Rat) : Rat :=
  a * d - b * c

example (a b c d k : Rat) :
    det (k*a) (k*b) (k*c) (k*d)
      = k ^ 2 * det a b c d := by
  taste? -- TryThis: grind +locals +suggestions
```
:::
::::

:::class "punch" "fragment"
The found tactic is _spliced back_ over `taste?` — the committed proof is concrete.
:::

:::fragment

```lean
theorem factorial_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ factorial n ⦃⇓result => ⌜result ≥ (1 : Int)⌝⦄ :=
  by
  mvcgen [factorial, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, result⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      (i ≥ (1 : Int) ∧ n -ₚ i +ₚ (1 : Int) ≥ (0 : Int)) ∧ result ≥ (1 : Int)⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr];
  sorry; sorry; omega
```

:::

# Proving monadic defs: `mvcgen`

%%%
state := "provemvcgen"
%%%

`do`-block functions use `Std.Do`'s `mvcgen` with Hoare triples `⦃P⦄ prog ⦃Q⦄`; Python contracts ride along as `Invariant` / `Ensures`:

::::hstack
:::class "excode" "fragment"
```code python
def sum_upto_n(n: int) -> int:
    Requires(n >= 0)
    total = 0
    for i in range(n + 1):
        Invariant(2*total == i*(i - 1))
        total += i
    Ensures(2*total == n*(n + 1))
    return total
```
:::

:::class "arrow-right" "fragment"
  →
_prove_
  →
:::

:::class "excode" "fragment"
```lean
theorem sum_upto_n_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ sum_to_n n ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [sum_to_n, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, total⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      (2 : Int) *ₚ total = i *ₚ (i -ₚ (1 : Int))⌝
  simp_all [taste_ingr]; grind +locals +suggestions
```
:::
::::

:::class "punch" "fragment"
`Invariant` / `Ensures` → {name}`pyPassInvariant` / {name}`pyPassEnsures`; `mvcgen` using Hoare Triples, discharges Goals to prove.
:::

# Proving in {lean}`PyAny` with `pyany_cases`

%%%
state := "pyanyproving"
vertical := some true
%%%

{lean}`PyAny` is not a commutative ring, so `ring`/`grind` stall on it directly. `pyany_cases` splits a goal into one goal _per relevant runtime type_; the mismatched tags close on their own:

:::class "step"
* All goals must be satisfied for the proof to be complete.
* They are unfolded from the instances supported by the operation applied to the {lean}`PyAny` variables.
* Any goal that makes no sense / has no instance is discharged automatically — e.g. `1 + "a"`.
* `pyany_cases` is wired into `taste?` — whenever {lean}`PyAny` appears, a best-effort proof attempt runs in the pipeline.
:::

::::hstack
:::class "excode" "fragment"
```lean
example (a b : PyAny) :
    (a +ₚ b) +ₚ b = a +ₚ (b +ₚ b) := by
  pyany_cases a b <;> grind +locals
```
:::

:::class "arrow-right" "fragment"
→
:::

:::class "excode" "fragment"

```code python
10 goals
case int.int
a b : ℤ
⊢ a + b + b = a + (b + b)
case int.bool
a : ℤ
b : Bool
⊢ ((a + if b = true then 1 else 0) + if b = true then 1 else 0) =
  a + ((if b = true then 1 else 0) + if b = true then 1 else 0)
...
```
:::
::::

# Recap

* _Deterministic transpiler_, not an LLM translator — the elaborator is the oracle.
* Broad language surface: control flow, comprehensions, exceptions, _classes_, libraries.
* Python behaviours like dynamic typing, multiple return types, and mutation are faithfully modeled in Lean with {lean}`PyAny`.
* _Monadic vs non-monadic_ picks the proof strategy:
  * Non-monadic pure function → `taste?`
  * Monadic functions in `do` blocks → `mvcgen`
* _LLMs propose contracts_; Lean checks them.

:::class "punch"
Pasta + Python + Lean = Python you can _prove_.
:::

# Thank you

:::class "subheader"
Questions?
:::

```html
<div class="finale"><img src="assets/pastaleanlogo.png" alt="PastaLean"></div>
```
