---
title: "PastaLean: Deterministic Transpilation from Python to Lean for Verification"
description: "How PastaLean turns ordinary Python into Lean 4 that both runs and can be proved: the pipeline, what it covers, the design decisions, and the benchmark numbers."
date: 2026-10-17
seoTitle: "PastaLean: a deterministic Python to Lean 4 transpiler that proves your code | Anirudh Gupta"
seoDescription: "How PastaLean turns ordinary Python into Lean 4 that both runs and can be proved: the pipeline, what it covers, the design decisions, and the benchmark numbers."
datePublished: 2026-10-17
series:
  name: "Building PastaLean"
  part: 1
crossPost: false
---

<style>
.pl-snip { margin: 1.4rem 0 1.8rem; border: 1px solid #d6d3d1; border-radius: 10px; overflow: hidden; background: #fff; }
.pl-snip iframe { display: block; width: 100%; border: 0; height: 420px; }
.pl-note { font-size: .9rem; font-style: italic; color: #78716c; margin: 0 0 .4rem; }
.pl-explorer label { font-size: .8rem; letter-spacing: .04em; text-transform: uppercase; color: #78716c; }
.pl-explorer select { font: inherit; font-size: .95rem; padding: .3rem .4rem; margin-left: .4rem;
                      border: 1px solid #d6d3d1; border-radius: 6px; max-width: 100%; background: #fff; }
.pl-ex[hidden] { display: none; }
.pl-ex h4 { font-size: .8rem; letter-spacing: .04em; text-transform: uppercase; color: #78716c; margin: 1.4rem 0 .5rem; }
</style>
A test tells you your code works on the inputs you thought of. A proof tells you it works on every
input there is. Almost nobody reaches for the second one, because the languages that can express a
proof — Lean 4, Rocq, Dafny, F\* — are not the languages anyone ships production code in. The logic
that needs checking is in Python.

An agent can translate that Python into Lean for you. The question is whether you trust the
translation.

<svg viewBox="0 0 660 148" role="img" aria-labelledby="gap-t gap-d" style="width:100%;height:auto;font-family:ui-sans-serif,system-ui,sans-serif">
  <title id="gap-t">Where the trust gap is</title>
  <desc id="gap-d">Python code becomes Lean code by a step marked with a question mark — who did the translation, and can you trust it? An agent then fills in the proof, and Lean checks that proof.</desc>
  <defs>
    <marker id="ah2" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="currentColor"/>
    </marker>
  </defs>
  <g style="color:var(--line,#64748b)" stroke="currentColor" fill="none" stroke-width="1.6">
    <rect x="8" y="40" width="176" height="58" rx="6"/>
    <path d="M 192 69 L 238 69" marker-end="url(#ah2)" stroke-dasharray="5 4"/>
    <rect x="246" y="40" width="168" height="58" rx="6"/>
    <path d="M 422 69 L 468 69" marker-end="url(#ah2)"/>
    <rect x="476" y="40" width="176" height="58" rx="6"/>
  </g>
  <g fill="var(--ink,#0f172a)" text-anchor="middle">
    <text x="96" y="68" font-size="15" font-weight="600">Python code</text>
    <text x="96" y="87" font-size="12" fill="var(--muted,#64748b)">what you actually wrote</text>
    <text x="330" y="68" font-size="15" font-weight="600">Lean code</text>
    <text x="330" y="87" font-size="12" fill="var(--muted,#64748b)">+ the correctness theorem</text>
    <text x="564" y="68" font-size="15" font-weight="600">Lean proof</text>
    <text x="564" y="87" font-size="12" fill="var(--muted,#64748b)">checked by Lean, not by you</text>
  </g>
  <text x="215" y="58" text-anchor="middle" font-size="22" font-weight="700" fill="var(--amber,#b45309)">?</text>
  <text x="215" y="120" text-anchor="middle" font-size="12" font-style="italic" fill="var(--amber,#b45309)">who translated it,<tspan x="215" dy="14">and do you trust it?</tspan></text>
  <text x="445" y="58" text-anchor="middle" font-size="12" fill="var(--muted,#64748b)">Agent</text>
  <text x="445" y="120" text-anchor="middle" font-size="12" font-style="italic" fill="var(--muted,#64748b)">may guess wrong,<tspan x="445" dy="14">cannot lie</tspan></text>
</svg>

What you need in the middle of that picture is a fixed, auditable tool: same input, same output,
every time, rather than a translation re-invented on each run. You state the correctness theorem, an
agent fills in the proof, and Lean checks the proof. The agent can still guess wrong; what it cannot
do is slip a wrong proof past the checker.

[PastaLean](https://github.com/siddhartha-gadgil/PastaLean) (Py + AST + Lean) is that tool. You
write ordinary Python. A fixed, deterministic translator turns it into Lean 4. Lean checks it, and
if you have said what the code is *supposed* to do, Lean proves it.

Before any explanation, here is what it does on three benchmarks of real Python:

| Dataset | Problems | Elaborated | Test cases | Passed |
|---|---|---|---|---|
| HumanEval⁺ | 164 | **151 (92.1%)** | 7,007 | **7,007 (100%)** |
| LeetCode | 2,589 | **2,391 (92.4%)** | 215,126 | **208,736 (97.0%)** |
| LiveCodeBench | 476 | **469 (98.5%)** | 10,213 | **10,213 (100%)** |

A program counts as *elaborated* when the Lean it produced type-checks, and a solution counts as
*passed* only when the runnable twin gives CPython's answer on **every one** of that problem's test
cases. A section near the end takes these apart, including what the failures are.

## Why this matters now

Most new Python is drafted by a model, and agentic systems lean on it harder still — write a
script, run it, read the number, build the next step on that number. If the script is subtly wrong
the conclusion is wrong, and nothing downstream notices. Testing is the usual answer and a weak one
here, because the tests come from the same process that wrote the bug.

Proving sounds unaffordable until you look at how agents spend their tokens. Only a small slice of
the code an agent generates feeds the final answer, and that slice is the only part worth proving.
Proving it blocks nothing, because verification runs in parallel with the exploration that follows.
File writes and network calls are not where the value is; the algorithm that processes the data is.

Lean 4 fits because it is two things at once: a proof assistant with Mathlib behind it, and a real
compiled language that goes through C to native code. The translated program runs at competitive
speed *and* can be reasoned about, reusing Mathlib rather than a verification stack built for this
one purpose.

## Why not ask a model to write the Lean?

This is the obvious shortcut, and rejecting it is the most important decision in the project.

**It is not reproducible.** Run a model twice and you get two translations. There is no line in any
table you can point at and say *this* is why `append` became `pyAppend`. Auditing a
non-deterministic translator audits one sample of it.

**It defeats the purpose.** A model translating Python to Lean may quietly fix the bug: clean up an
off-by-one, pick the sensible branch, write the code you obviously meant. Desirable in an assistant,
fatal in a verifier. A model can translate incorrect Python into correct Lean — the proof closes,
you ship, and the bug is still in the Python that runs. A better model makes this rarer rather than
impossible, and from the outside you cannot tell which translation you got.

**It measures poorly.** We ran Claude Opus 4.8 on HumanEval⁺ and LiveCodeBench through the same
harness PastaLean is scored with, signature pinned in the prompt so the output is callable, five
independent samples per problem at temperature 1.0.

| | HumanEval⁺ | LiveCodeBench |
|---|---|---|
| LLM, pass@1 — one sample works | 75.4% | 52.5% |
| LLM, pass@5 — at least one of five works | 87.2% | 74.9% |
| LLM, pass⁵ — **all five** work | 62.8% | 31.4% |
| PastaLean, generated Lean compiles | **92.1%** | **98.5%** |
| PastaLean, test cases matching CPython | **100%** | **100%** |

The number to look at is the distance between pass@5 and pass⁵. On LiveCodeBench the model finds a
working translation within five tries three-quarters of the time, and produces five that all work
less than a third of the time. That spread *is* the unreliability, and a deterministic transpiler
has pass⁵ equal to pass@1 by construction, because there is only ever one output.

Writing in Dafny from the start only moves the risk to the specification: if the spec is
mistranslated from what you meant, the code is provably correct about the wrong thing and nothing
flags it. The specification itself can be written in either language — Python when you want every
reviewer to read it, Lean when you need mathematics Python has no notation for. PastaLean picks up
both.

## The pipeline

Transpilation runs in four stages, from Python's own abstract syntax tree to Lean.

<svg viewBox="0 0 660 272" role="img" aria-labelledby="pipe-t pipe-d" style="width:100%;height:auto;font-family:ui-sans-serif,system-ui,sans-serif">
  <title id="pipe-t">The PastaLean pipeline</title>
  <desc id="pipe-d">Python source is parsed to an AST and JSON IR; TypeInfer annotates it and the code generator emits Lean 4 as a provable twin and a runnable twin; if the Python carries contracts, the pipeline continues into a machine-checked proof.</desc>
  <defs>
    <marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="currentColor"/>
    </marker>
  </defs>
  <g style="color:var(--line,#64748b)" stroke="currentColor" fill="none" stroke-width="1.6">
    <rect x="60" y="8" width="200" height="36" rx="6" stroke-dasharray="5 4"/>
    <path d="M 160 44 L 160 62" marker-end="url(#ah)"/>
    <rect x="60" y="66" width="200" height="56" rx="6"/>
    <rect x="400" y="66" width="200" height="56" rx="6"/>
    <path d="M 266 94 L 393 94" marker-end="url(#ah)"/>
    <path d="M 500 122 C 500 156 160 156 160 184" marker-end="url(#ah)"/>
    <rect x="60" y="188" width="200" height="64" rx="6"/>
    <rect x="400" y="188" width="200" height="64" rx="6" stroke-dasharray="5 4"/>
    <path d="M 266 220 L 393 220" marker-end="url(#ah)"/>
  </g>
  <g fill="var(--ink,#0f172a)" text-anchor="middle">
    <text x="160" y="31" font-size="13" font-style="italic" fill="var(--muted,#64748b)">contracts (optional)</text>
    <text x="160" y="90" font-size="15" font-weight="600">Python source</text>
    <text x="160" y="110" font-size="12" fill="var(--muted,#64748b)">ordinary, unmodified</text>
    <text x="500" y="90" font-size="15" font-weight="600">AST → JSON IR</text>
    <text x="500" y="110" font-size="12" fill="var(--muted,#64748b)">one node per construct</text>
    <text x="160" y="212" font-size="15" font-weight="600">Lean 4</text>
    <text x="160" y="230" font-size="12" fill="var(--muted,#64748b)">provable twin +</text>
    <text x="160" y="245" font-size="12" fill="var(--muted,#64748b)">runnable twin</text>
    <text x="500" y="214" font-size="15" font-weight="600">Proof</text>
    <text x="500" y="234" font-size="12" fill="var(--muted,#64748b)">machine-checked</text>
  </g>
  <g fill="var(--muted,#64748b)" text-anchor="middle" font-size="12">
    <text x="330" y="88">parse</text>
    <text x="330" y="150">TypeInfer annotates, then codegen emits</text>
    <text x="330" y="214">prove, if contracts</text>
  </g>
</svg>

**Parse.** Python's own `ast` module does it, so there is no second grammar to keep in sync with
CPython. The tree becomes JSON, one object per node.

**Annotate.** Lean needs a type for every binder; Python supplies almost none. A type inference
engine, `TypeInfer`, walks the IR and writes a type onto every binder it can work out — and changes
nothing else. No expression is rewritten, no node removed. The generator reads an inferred type in
exactly the place it reads a hand-written annotation, so a fully annotated program produces
identical Lean whether the engine ran or not.

**Generate.** Each kind of IR node has one Lean function registered against it, and a dispatcher
looks it up and recurses into children. Supporting new syntax means writing one function. Those
functions return Lean's own typed syntax objects rather than strings, so a generator cannot emit
something that is not well-formed Lean.

**Elaborate.** The output goes through Lean's elaborator, which decides whether it type-checks
against the runtime. This is the paradigm the project rests on: **the Lean elaborator is the
oracle.** We are not comparing output against golden files written by hand. We are asking a compiler
whether the translation makes sense, and it answers for every program, including the ones nobody
thought to test.

Loading Mathlib costs four to five seconds, so the generator runs as one persistent backend that
statements stream into, paying that once per dataset rather than once per file. It sustains about
12,000 IR nodes per second — an average solution file converts in roughly 10 milliseconds.

### A worked example

HumanEval 85 — *add the even elements at odd indices* — with its specification written in the
Python:

```python
from contracts import *

def add(lst):
    Requires(len(lst) > 0)
    # THE POINT: only even elements are ever added, so the answer is even.
    Ensures(Result() % 2 == 0)

    s = 0
    for i in range(1, len(lst), 2):
        Invariant(s % 2 == 0)          # the running sum stays even
        Invariant(1 <= i)              # index bounds, so lst[i] is defined
        Invariant(i < len(lst))
        Invariant(i % 2 == 1)          # range(1, _, 2) yields only odd indices
        if lst[i] % 2 == 0:
            s += lst[i]
    return s
```

`Requires`, `Ensures` and `Invariant` are thin wrappers around `assert`, so the file still runs
under CPython exactly as before. The translator does not evaluate them: it lifts them out of the
syntax tree and turns them into the statement of a theorem.

<p class="pl-note">Hover or click any name below for its real type, docstring or proof state — this is the Lean compiler's own data.</p>
<div class="pl-snip"><iframe src="/src/blogs/pastalean-proving-python-correct/pipeline.html" title="Interactive Lean snippet" loading="lazy"></iframe></div>

The loop is a real Lean `for` loop over mutable state; the operators carry a small `ₚ` to mark
Python semantics. Read the theorem as a sentence: *assuming the list is non-empty, running `add` on
it gives back an `s` that is even.* The pre- and postcondition came from the `Requires` and
`Ensures` lines, the bullet under `mvcgen` from the `Invariant` calls, and the tactic line closes
what remains.

Nothing about this is a test. There is no list of inputs. The statement covers every list of
integers that exists.

## What PastaLean covers

The target is the part of Python that logic is actually written in, not the part that moves bytes
around.

| | Covered |
|---|---|
| **Values** | `int`, `float`, `bool`, `str`, `list`, `dict`, `set`, tuples, slicing, f-strings, chained comparisons, Python's own `//`, `%` and `**` |
| **Control flow** | `if`/`elif`/`else`, `for`, `while`, `break`/`continue`, `match`, list/dict/set comprehensions, generator expressions |
| **Functions** | default arguments, several `return`s of different types, nested functions, closures, currying, decorators, `lambda`, `yield`, `@cache` |
| **Objects** | classes, `__init__`, methods, `@staticmethod`/`@classmethod`/`@property`, dunder operators, single and multiple inheritance |
| **Effects** | `try`/`except`/`finally`, `raise`, `print`, `input` |
| **Libraries** | `math`, `typing`, `heapq`, `numpy`, `pandas`, `scipy`, and anything else somebody writes a mapping for |
| **Contracts** | `Requires`, `Ensures`, `Invariant`, `Decreases`, `Assert` — all written in Python |

What is *not* covered is the code that reshapes itself as it runs: `eval`, `exec`, monkey-patching,
attribute names computed at run time, `async`/`await` and threads. None of it has a static meaning
to translate.

Coverage here means more than "it parses". Python's semantics are reproduced where they differ from
Lean's, and the differences are the dangerous part, because both conventions are defensible and
neither raises an error:

<div class="pl-snip"><iframe src="/src/blogs/pastalean-proving-python-correct/operators.html" title="Interactive Lean snippet" loading="lazy"></iframe></div>

`7 // -2` is `-4` in Python and `-3` in Lean; `7 % -2` is `-1` against `1`. Mathlib already defines
addition on lists **pointwise**, so left alone `[1,2] + [3,4]` would quietly become `[4,6]` instead
of `[1,2,3,4]` — a wrong answer no type error catches, in a program that compiles cleanly. Getting
Python's reading to win is not a detail; it is the semantics. Every operator, builtin and container
method above is a decision of that kind, each backed by tests against CPython.

## Design decisions

Python and Lean disagree about mutation, types, objects, effects and numbers. Five of those
disagreements shaped everything else, and each was settled in whichever direction protects
provability.

**Every function is translated twice.** One Python function becomes two Lean definitions: a
**provable** twin and a **runnable** one, from the same IR and the same generators.

<div class="pl-snip"><iframe src="/src/blogs/pastalean-proving-python-correct/twins.html" title="Interactive Lean snippet" loading="lazy"></iframe></div>

The two jobs want opposite things. For proving, a Python `float` becomes an exact rational, because
IEEE floating point says `0.1 + 0.2` is not `0.3` and you cannot build a proof on arithmetic that is
approximately true; and a list becomes the structure Mathlib's lemmas are stated about. For running,
both are slow — that structure is a linked list, so a loop that is linear in Python becomes
quadratic. The runnable twin uses arrays and gets Python's performance. Effects split the same way:
printing and raising are real in the runnable twin and no-ops in the provable one, which is what
lets a theorem talk about what a program prints.

**Effects are pushed to the edges.** Each function is lowered to the weakest shape that can express
it — a plain computation if it only computes, local mutation if it has loops, exceptions if it
raises, real I/O only if it talks to the outside world. Pure functions are far easier to prove about
than effectful ones, which is both the argument for the design and advice on how to structure the
Python you intend to verify.

**The runtime is written in Lean, not called through a bridge.** Over 200 Lean definitions
implement Python's builtins and container methods. The obvious objection is that you could call into
CPython through a foreign function interface and get Python's exact behaviour for free. You could,
and the program would run perfectly. It would also **prove nothing at all**: to a proof, a foreign
call is an opaque constant with no equations attached — nothing to unfold, nothing to rewrite. The
runnable twin would be flawless and the provable twin empty. Written as ordinary Lean definitions
they can be unfolded, and each ships a small lemma rewriting a generated operator back into Lean's
own arithmetic so `ring` or `omega` can finish the goal. Those same steps — a definition, one arm in
a lookup table, `#eval` checks against Python — are the entire extension story, which is why no
library name appears anywhere in the code generator.

**Mutation and scoping are handled, not banned.** `xs.append(3)` becomes a rebuild of `xs` rebound
to the same name. That reads as though it copies the list on every append and does not: because
nothing else holds the old value, Lean's reference counting updates the buffer in place. A variable
first assigned inside an `if` or a `for` is still visible after the block in Python but not in Lean,
so it is hoisted automatically.

**Objects are values by default; the heap is opt-in.** A class becomes a structure plus a namespace
of functions, and a method that mutates `self` returns an updated object. That is exact for as long
as each object has one name, which covers most of the code we target. Here is where it stops:

```python
a = Counter()
b = a               # Python: one object, two names
b.inc()
b.inc()
a.get()             # Python says 2. Copy-on-assignment would say 0.
```

Python passes objects by reference, so `b` *is* `a` — the one kind of mistranslation no type error
catches. So reference semantics is a second tier you switch on, `--heap`, where objects live behind
a typed reference and `b = a` copies an address. An analysis across calls decides which functions
actually touch the heap, so pure helpers keep their pure translation. A program pays for a heap only
when it has one.

**And a line with no translation does not stop the file.** Real Python is full of statements that
carry no logic — logging, a progress print, a metrics call — and a translator that halted at the
first `logging.getLogger` would be useless on exactly the code worth verifying. Such a line becomes
a placeholder holding its own source text: the binding still elaborates, the variable stays
declared, a linter warns you, and the loop doing the real work is verified as normal. `--strict`
turns the placeholder into a hard error. The cost is measured rather than asserted — **5 of 2,589**
LeetCode problems are skipped for importing something outside the supported set, and HumanEval
translates with **zero** placeholders.

## Does it work?

**How do you know PastaLean is correct?** We cannot prove it. That would need a formal semantics for
Python written inside Lean, and nobody has written one. PastaLean does not model all of Python, and
compressing a dynamically typed object-oriented language into a statically typed one is a pile of
judgement calls. So the honest answer is empirical.

The table at the top of this post is that answer. Averaged across the three datasets, 94.3% of
programs elaborate and 99.0% of test cases agree; pooled over all 3,229 programs and 232,346 test
cases it is 93.2% and 97.2%, since LeetCode is most of the mass. Every LeetCode disagreement is
recorded with the input that separated it, and each points at a specific runtime function returning
a wrong value rather than at a limit of the translation.

The failure analysis is the more useful result. The 13 HumanEval programs that do not elaborate are
mostly not generator bugs. They are genuine type ambiguities:

```python
def split_words(txt):
    # words on whitespace, else on commas, else a letter count
    if any(c in txt for c in ' \n\r\t'): return txt.split()
    if ',' in txt: return txt.split(',')
    return sum(1 for c in txt if c.islower() and (ord(c) - ord('a')) % 2 == 1)
```

For most inputs this returns a list of strings. For an input with no spaces and no commas it returns
an integer. Both are correct Python, and nothing in the code or the signature says which one this
function *is* — it depends on the input, at run time. Lean needs one return type.

Add a single type hint at the ambiguous spot and all 13 compile: **164 of 164**. That is the honest
shape of the limitation. It is not "the tool is 92% good". It is "92% of these need nothing from
you, and the rest need one word."

## Two proofs, start to finish

Two complete problems, the two hardest of the five the paper takes end to end. Read each in two
steps: the Python with its contract attached, then the Lean that came out of it with the proof that
closes it. Nothing is abridged — each is the committed file exactly as it stands, interactive
because it compiles.

<div class="pl-explorer"><label for="pl-exsel">Explore a proved problem:</label> <select id="pl-exsel"><option value="count_up_to">count_up_to — a prime sieve (HumanEval/96)</option><option value="double_the_difference">double_the_difference — a function restated as a sum (HumanEval/151)</option></select></div>

<section class="pl-ex" id="pl-ex-count_up_to">
<p class="pl-note">Nested loops. Six invariants on the outer loop and two on the inner, and from them three postconditions: the answer is no longer than n, and every entry lies in the window 2 … n-1.</p>
<h4>1 &middot; The Python, carrying its contract</h4>

```python
from typing import *
from contracts import *

def count_up_to(n: int):
    """The first n primes less than n."""
    Requires(n >= 0)
    # THE POINT: the sieve only ever appends its own loop counter, which runs over {2, ..., n-1},
    # and at most once per value — so the answer lies in that window and is no longer than n.
    Ensures(len(Result()) <= n)
    Ensures(all(2 <= p for p in Result()))
    Ensures(all(p < n for p in Result()))
    ans = []
    isprime = [True] * (n + 1)
    for i in range(2, n):
        Invariant(2 <= i)
        Invariant(i <= n)
        Invariant(len(isprime) == n + 1)
        # At most one append per counter value.
        Invariant(len(ans) <= i)
        # Everything appended so far was a counter value already passed.
        Invariant(all(2 <= p for p in ans))
        Invariant(all(p < i for p in ans))
        if isprime[i]:
            ans.append(i)
            for j in range(i + i, n, i):
                # Index bound for `isprime[j]`.
                Invariant(2 <= j)
                Invariant(j < n)
                isprime[j] = False
    return ans
```

<h4>2 &middot; The Lean it becomes, and the proof that closes it</h4>
<div class="pl-snip"><iframe src="/src/blogs/pastalean-proving-python-correct/ex_count_up_to.html" title="Lean translation and proof" loading="lazy"></iframe></div>
</section>

<section class="pl-ex" id="pl-ex-double_the_difference" hidden>
<p class="pl-note">The postcondition restates the entire function as a summation, so proving it means proving the loop computes that sum and nothing else. The heaviest of the paper&#x27;s five.</p>
<h4>1 &middot; The Python, carrying its contract</h4>

```python
from contracts import *

def double_the_difference(lst):
    '''Sum of squares of the odd numbers in lst; negatives and non-integers are ignored.'''
    # No precondition: the recorded inputs mix ints, floats and negatives, so any `Requires`
    # restricting the element type would be false. The result is the sum of squares over exactly
    # the positive odd integers of `lst`, hence a sum of odd squares.
    Ensures(Result() == sum([v * v for v in lst if v % 2 == 1 and v > 0 and "." not in str(v)]))
    # An odd square is odd, so the parity of the answer is the parity of the number of contributors.
    Ensures(Result() % 2 == len([v for v in lst if v % 2 == 1 and v > 0 and "." not in str(v)]) % 2)
    Ensures(Result() >= 0)

    ans = 0
    for num in lst:
        Invariant(ans >= 0)
        if num % 2 == 1 and num > 0 and "." not in str(num):
            ans += num ** 2

    Assert(ans >= 0)
    return ans
```

<h4>2 &middot; The Lean it becomes, and the proof that closes it</h4>
<div class="pl-snip"><iframe src="/src/blogs/pastalean-proving-python-correct/ex_double_the_difference.html" title="Lean translation and proof" loading="lazy"></iframe></div>
</section>

Watch where the human work goes. The theorem statement is generated from the `Requires` and
`Ensures` lines; each `Invariant(...)` becomes one bullet of the `mvcgen` call. What is left for a
person, or a model with a person checking it, is the tactic script underneath — the argument for
*why* those invariants survive a round of the loop and together give the postcondition. That is the
one step nobody has automated.

## `TypeInfer`: the type inference engine

Lean fixes a function's parameter types *before* it looks at the body, so every binder needs a type
up front. Python supplies almost none, and the hints it does supply are not enforced:

```python
def add(a: int, b: int) -> int:
    return a + b

add("Hi", "!")      # this works fine. Python does not check the hints.
```

A hint is evidence, not truth, and most code carries none. `TypeInfer` recovers the rest from how
values are used, and because the engine is written in Lean, the laws it rests on are
**machine-checked**: widening a type never excludes a value the program can produce. When no single
type exists — a parameter used at incompatible types by different callers, a function returning a
string on one path and an integer on another — the value is boxed rather than rejected, so the
program still compiles and runs. That costs provability, not translation.

Two benchmarks measure it, and they test different things. TypeEvalPy is per file: every
ground-truth annotation is one *fact* keyed by its source location, and a tool is scored by how many
it recovers by exact match. On the autogen set (5,453 snippets, 77,268 facts) `TypeInfer` is the
best static tool on the leaderboard.


| Tool | Return | Param | Var | Matched | Match |
|---|---|---|---|---|---|
| **TypeInfer** | **16,220** | **404** | **39,560** | **56,184** | **72.7%** |
| HeaderGen | 14,086 | 346 | 36,370 | 50,802 | 65.7% |
| Jedi | 13,160 | 0 | 15,403 | 28,563 | 37.0% |
| Scalpel | 15,383 | 171 | 18 | 15,572 | 20.2% |
| Type4Py | 3,143 | 38 | 2,243 | 5,424 | 7.0% |


That is 5,382 facts ahead of HeaderGen, the previous static leader, and 12th of 26 on the full board
— above several instruction-tuned language models, while producing one deterministic type per fact
with no model and no sampling. It is also the fastest on that run, 1.25 s against HeaderGen's 36.2 s.
Returns are **90.1%**, because a return type is pinned by the body you are already looking at. Parameters are **45.1%** and are the hardest category for *every* tool
there, for the reverse reason: a parameter's type is evidence from call sites, and nothing inside
the function states it. Against the newer production checkers the picture splits, and it is worth
stating plainly: pyrefly recovers more *variable* types and takes the overall total, 78.6% to 72.7%,
while `TypeInfer` leads on returns and parameters, the two a transpiler needs.

The second benchmark is the one that matters for real code, because a type usually has to cross a
file boundary to be recovered at all. TypyBench strips the annotations from 50 real projects (67,897
slots) and scores graded similarity between inferred and true type trees.

<svg viewBox="0 0 660 133" role="img" aria-labelledby="ti-repo-t ti-repo-d" style="width:100%;height:auto;font-family:ui-sans-serif,system-ui,sans-serif">
  <title id="ti-repo-t">TypyBench: accuracy, speed and memory</title>
  <desc id="ti-repo-d">Three bar charts over 50 real projects: TypeSim similarity, wall-clock time on a log scale, and peak memory. TypeInfer is most accurate and fastest, and second lightest after hityper.</desc>
  <text x="0" y="14" font-size="11" font-weight="600" fill="#1c1917">TypeSim</text>
  <text x="0" y="27" font-size="9.5" fill="#78716c">higher is better</text>
  <text x="57" y="43" font-size="9.5" text-anchor="end" fill="#1c1917" font-weight="600">TypeInfer</text>
  <rect x="62" y="34" width="128.0" height="12" rx="2" fill="#a16207"/>
  <text x="194.0" y="43" font-size="9" fill="#1c1917">0.284</text>
  <text x="57" y="62" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyrefly</text>
  <rect x="62" y="53" width="109.5" height="12" rx="2" fill="#c7c2bc"/>
  <text x="175.5" y="62" font-size="9" fill="#78716c">0.243</text>
  <text x="57" y="81" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyre</text>
  <rect x="62" y="72" width="107.7" height="12" rx="2" fill="#c7c2bc"/>
  <text x="173.7" y="81" font-size="9" fill="#78716c">0.239</text>
  <text x="57" y="100" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pytype</text>
  <rect x="62" y="91" width="71.2" height="12" rx="2" fill="#c7c2bc"/>
  <text x="137.2" y="100" font-size="9" fill="#78716c">0.158</text>
  <text x="57" y="119" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">hityper</text>
  <rect x="62" y="110" width="47.3" height="12" rx="2" fill="#c7c2bc"/>
  <text x="113.3" y="119" font-size="9" fill="#78716c">0.105</text>
  <text x="220" y="14" font-size="11" font-weight="600" fill="#1c1917">Wall clock</text>
  <text x="220" y="27" font-size="9.5" fill="#78716c">log scale, lower is better</text>
  <text x="277" y="43" font-size="9.5" text-anchor="end" fill="#1c1917" font-weight="600">TypeInfer</text>
  <rect x="282" y="34" width="8.1" height="12" rx="2" fill="#a16207"/>
  <text x="294.1" y="43" font-size="9" fill="#1c1917">135s</text>
  <text x="277" y="62" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyrefly</text>
  <rect x="282" y="53" width="22.2" height="12" rx="2" fill="#c7c2bc"/>
  <text x="308.2" y="62" font-size="9" fill="#78716c">228s</text>
  <text x="277" y="81" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyre</text>
  <rect x="282" y="72" width="25.6" height="12" rx="2" fill="#c7c2bc"/>
  <text x="311.6" y="81" font-size="9" fill="#78716c">259s</text>
  <text x="277" y="100" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pytype</text>
  <rect x="282" y="91" width="80.8" height="12" rx="2" fill="#c7c2bc"/>
  <text x="366.8" y="100" font-size="9" fill="#78716c">2,015s</text>
  <text x="277" y="119" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">hityper</text>
  <rect x="282" y="110" width="128.0" height="12" rx="2" fill="#c7c2bc"/>
  <text x="414.0" y="119" font-size="9" fill="#78716c">11,652s</text>
  <text x="440" y="14" font-size="11" font-weight="600" fill="#1c1917">Peak memory</text>
  <text x="440" y="27" font-size="9.5" fill="#78716c">GiB, lower is better</text>
  <text x="497" y="43" font-size="9.5" text-anchor="end" fill="#1c1917" font-weight="600">TypeInfer</text>
  <rect x="502" y="34" width="29.0" height="12" rx="2" fill="#a16207"/>
  <text x="535.0" y="43" font-size="9" fill="#1c1917">0.70</text>
  <text x="497" y="62" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyrefly</text>
  <rect x="502" y="53" width="128.0" height="12" rx="2" fill="#c7c2bc"/>
  <text x="634.0" y="62" font-size="9" fill="#78716c">3.09</text>
  <text x="497" y="81" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pyre</text>
  <rect x="502" y="72" width="76.2" height="12" rx="2" fill="#c7c2bc"/>
  <text x="582.2" y="81" font-size="9" fill="#78716c">1.84</text>
  <text x="497" y="100" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">pytype</text>
  <rect x="502" y="91" width="52.6" height="12" rx="2" fill="#c7c2bc"/>
  <text x="558.6" y="100" font-size="9" fill="#78716c">1.27</text>
  <text x="497" y="119" font-size="9.5" text-anchor="end" fill="#78716c" font-weight="400">hityper</text>
  <rect x="502" y="110" width="7.9" height="12" rx="2" fill="#c7c2bc"/>
  <text x="513.9" y="119" font-size="9" fill="#78716c">0.19</text>
</svg>


The per-file numbers say the inference itself is right. The repository numbers say the pass that
flows types across imports is right, and that is the one a transpiler depends on, since a function
you call is usually defined in another file. The speed comes from what the engine does not do: it
never loads Mathlib, starts in 30 milliseconds, and runs thousands of files as independent tasks in
one process, where the checkers it is compared against load a full checking state per worker. The
known gap, plainly: no union types yet, so `int` joined with `str` is boxed rather than typed
`int | str`.

## What this changes

The division of labour falls out of the design. **The model writes the Python. You state the
specification. A fixed translator does the translation. An agent searches for the proof, and Lean
decides.** Each party does the thing it is reliable at, and the model is never in the trusted path
for *meaning*.

The contract is the real interface, and its being Python is underrated. It is the one artifact a
human has to read and agree with, and the review question is small and concrete: *does this sentence
say what I wanted?* Your job shifts from "is this code correct" to "is this the right notion of
correct". If the code does not meet the specification, Lean refuses the proof. If the specification
says the wrong thing, Lean will prove the wrong thing just as happily — which is why the contract is
the artifact a human must read.

PastaLean ships an MCP server, so a model can drive the whole loop itself: annotate, translate, read
back the open obligations, attempt them, call the verifier. One rule makes that loop worth running —
**the checker's verdict is the only verdict**. A model reporting that something is proved is not
evidence; `verify_theorems` is.

### What's next

- Union types, so `int | str` stops being boxed.
- Dynamic dispatch and multiple inheritance, the two object-model gaps.
- Stronger proof automation; the tactic script is still the step a human writes.
- Certificates for the type checker's verdicts, so a clean file carries a re-checkable record of why.

If you want to try it on your own code, `uv run pastalean translate prog.py` is the whole of the
first step.

---

*PastaLean is open source at [github.com/siddhartha-gadgil/PastaLean](https://github.com/siddhartha-gadgil/PastaLean)*.
*Paper: [PastaLean](https://openreview.net/forum?id=7vrdqmHlL1).*

<script>
(function () {
  // The snippets are self-contained pages in an iframe: they report their height,
  // and they take their colour scheme from the page (this site is light-only).
  var frames = Array.prototype.slice.call(document.querySelectorAll('.pl-snip iframe'));
  function light(f) {
    try { f.contentWindow.postMessage({ type: 'snippet-theme', theme: 'light' }, '*'); } catch (e) {}
  }
  window.addEventListener('message', function (e) {
    var d = e && e.data;
    if (!d || d.type !== 'snippet-height' || !d.height) return;
    frames.forEach(function (f) { if (f.contentWindow === e.source) f.style.height = (d.height + 8) + 'px'; });
  });
  frames.forEach(function (f) { f.addEventListener('load', function () { light(f); }); light(f); });

  var sel = document.getElementById('pl-exsel');
  if (sel) sel.addEventListener('change', function () {
    Array.prototype.forEach.call(document.querySelectorAll('.pl-ex'), function (s) {
      var on = s.id === 'pl-ex-' + sel.value;
      s.hidden = !on;
      if (on) { var f = s.querySelector('iframe'); if (f) setTimeout(function () { light(f); }, 60); }
    });
  });
})();
</script>
