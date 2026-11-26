# The postcondition reads a local (`r`), which the checker cannot see after the call: refute checks it
# in a copy of the function that returns the postcondition at each `return` (`pl_post_isqrt`).
from contracts import *


def isqrt(n: int) -> int:
    Requires(n >= 0)
    Ensures(r * r <= n < (r + 1) * (r + 1) and Result() == r)
    r = 0
    while (r + 1) * (r + 1) < n:
        r += 1
    return r
