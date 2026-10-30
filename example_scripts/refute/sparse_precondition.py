from contracts import *


# The bug is only reachable inside a narrow precondition (price ≥ 1000, ≡ 3 mod 97, above 1200), which
# small-scope enumeration and plain random draws almost never satisfy.
def discount(price: int) -> int:
    Requires(price >= 1000)
    Requires(price % 97 == 3)
    Ensures(Result() >= 0)
    if price > 1200:
        return price - 2000
    return price
