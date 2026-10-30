from typing import List


def basic_types():
    a = 1
    b = 2.5
    c = "hello"
    d = True
    e = [1, 2]
    f = (1, "a")
    g, h = 3, 4.5
    m, n, p = 5, "world", False
    tup1 = ("foo", 42)
    tup2 = (g, h)

def starred_unpacking(lst: List[int]):
    # `*` collects the middle into a list; elements after the star read from the end, so `last` is
    # always `lst[-1]` regardless of length. `head, *body, last = [1,2,3,4]` → (1, [2,3], 4).
    head, *body, last = lst
    first, *rest = lst
    *init, tail = lst
    return head, body, last, rest, init


def fstring():
    s1 = "Hello"
    s2 = "World"
    s3 = s1 + ", " + s2 + "!"
    return f"This is a string: {s3} and this is a number: {1+2}"

def annotated_vars():
    x: int = 10
    y: int = 20
    return x + y


# Python's numeric tower: int values coerce up to float. These guard the T1 mixed int/float codegen
# coercions the leetcode DP corpus depends on — regressions here are otherwise only caught by rerunning
# the corpus.

def numeric_tower_widening(flags: List[bool], a: int, b: int) -> int:
    # Python's numeric tower `bool < int < float < ℚ`: a `bool` widens into an int accumulator, and
    # bool comparison results take part in arithmetic. `sum` of bools counts them.
    total = 0
    for f in flags:
        total += f                     # bool → int
    return total + (a > b) + (a == b) * 2


def mixed_scalar_accumulator(xs: List[int]) -> float:
    # int-seeded `ans` joins a float (`x / 2`) → must become float; the `0` seed coerces to `(0 : ℚ)`.
    ans = 0
    for x in xs:
        ans = max(ans, x / 2)
    return ans


def int_init_float_container(nums: List[int]) -> List[float]:
    # `dp = [0]*n` later holds floats (`/ 2`) → `List float`, with the `0` element coerced.
    n = len(nums)
    dp = [0] * n
    for i in range(1, n):
        dp[i] = dp[i - 1] / 2 + nums[i]
    return dp


def heterogeneous_pyany():
    # `[1, "hi", 3]` is `List PyAny`; arithmetic on a boxed element (`* 2`, `+`) dispatches on the tag.
    xs = [1, "hi", 3]
    total = 0
    total = total + xs[0] * 2
    return total


def untyped_param_arithmetic(nums):
    # `nums` is un-inferred → boxed `PyAny`; the two-pass seed propagates `PyAny` to the accumulator so
    # `total` is `PyAny` (not `Int`), matching the boxed element arithmetic.
    total = 0
    for x in nums:
        total += x * 2
    return total


def untyped_param_compare_and_div(nums):
    # Comparison, `%` and `/` on boxed (`PyAny`) values; `best` is a `let mut PyAny` slot reassigned
    # across the loop (not shadowed).
    best = 0
    for x in nums:
        if x > best:
            best = x + x % 3
    return best / 2


def untyped_param_bitwise(nums):
    # Bitwise (`| & `), floor-div (`//`) and shift on boxed (`PyAny`) values.
    r = 0
    for x in nums:
        r = (r | (x & 1)) + x // 2
    return r << 1


def grid_float_dp(m: int, n: int) -> float:
    # 2D grid DP initialised int (`[[0]*n ...]`) that becomes float via `/ 2` — the nested
    # `f[i][j] = ...` teaches `f : list[list[float]]`, coercing the innermost `0`.
    f = [[0] * n for _ in range(m)]
    f[0][0] = 1
    for i in range(m):
        for j in range(n):
            if i > 0:
                f[i][j] += f[i - 1][j] / 2
    return f[m - 1][n - 1]


# --- Back-inference from comparisons (unannotated params pinned by `== <literal>` / `in`) ---
# Each param below is UN-annotated; its type is recovered from a comparison against a literal, so the
# body type-checks WITHOUT boxing to PyAny. If the inference regressed, `PyAny == <literal>` would not
# compile — so these compiling IS the regression test, one per PyAny subtype.

def eq_pins_str(s):
    # `s == "hello"` ⇒ s : str, so `.upper()` (a str-only method) resolves.
    return s.upper() if s == "hello" else s

def eq_pins_int(x):
    # `x == 42` ⇒ x : int, so the int-only shift `x << 1` type-checks.
    return x << 1 if x == 42 else x

def eq_pins_float(v):
    # `v == 3.14` ⇒ v : float.
    return v * 2.0 if v == 3.14 else v

def eq_pins_list_elem(xs):
    # `xs == []` ⇒ xs : list; `xs[0] + 1` pins the ELEMENT to int ⇒ xs : list[int] (no PyAny box).
    return 0 if xs == [] else xs[0] + 1

def eq_pins_list_nested(a):
    # Element int recovered from a NESTED int-forcing op: `(a[0] + a[-1]) % 2` (the SortArray pattern).
    return (a[0] + a[-1]) % 2 if a != [] else 0

def eq_pins_list_method(words):
    # `words[0].upper()` — a str-only method on an element ⇒ words : list[str].
    return words[0].upper() if words != [] else ""

def membership_pins_str(ch):
    # `ch in "aeiou"` ⇒ ch is an element of a str literal ⇒ ch : str.
    return 1 if ch in "aeiou" else 0

def reassign_type_change_still_ok():
    # SAFETY: a type-CHANGING reassignment must keep working — `m` is str then int. Back-inference must
    # not clobber it (codegen's rebind-shadow re-types the post-`int(m)` segment).
    m = "1"
    m = int(m)
    return m ** 2
