from contracts import *


# False contracts whose counterexamples sit on nonlinear integer constraints: grind's linear solver
# returns spurious models here, and random draws rarely land on the few violating inputs.
# `pastalean refute --smt` gets each from an SMT model that Lean then evaluates and kernel-certifies.
def pythag(a: int, b: int, c: int) -> bool:
    Requires(0 < a and a < b and b < c and c < 100)
    Ensures(Result() == False)
    return a * a + b * b == c * c and a + b + c == 84


def semiprime(a: int, b: int) -> int:
    Requires(1 < a and a <= b)
    Ensures(Result() != 391)
    return a * b


def taxicab(x: int, y: int) -> int:
    Requires(0 < x and x < y)
    Ensures(Result() != 4104)
    return x * x * x + y * y * y


def quadratic_root(x: int) -> int:
    Requires(x > 1000)
    Ensures(Result() != 0)
    return x * x - 2026 * x + 26169


def mod_square(x: int) -> bool:
    Requires(0 <= x and x < 10000)
    Ensures(Result() == False)
    return x % 97 == 13 and (x * x) % 101 == 5


def tagged(s: str, n: int) -> int:
    Requires(n * n == 49)
    Ensures(Result() == 0)
    if s.startswith("id-") and len(s) == n and s.endswith("9"):
        return 1
    return 0


def slug(s: str) -> int:
    Ensures(Result() != 7)
    if "--" in s and s[2:5] == "abc":
        return s.find("--")
    return 0
