# A pure caller of a contracted (`Id`-typed) function: the call must read its value, not the action.
from contracts import *


def classify(a: int, b: int) -> int:
    Ensures(Result() >= 0)
    if a > 1000:
        if b == 3:
            return -1
    return 1


def is_nonneg(a: int, b: int) -> bool:
    r = classify(a, b)
    return r >= 0


def shifted(a: int, b: int) -> int:
    return classify(a, b) + 1
