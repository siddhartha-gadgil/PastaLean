# A bug behind three nested conditions: random and hill-climbing search on the result alone never reach
# it; the branch-coverage engine climbs one condition at a time (with the literal 13 as its step).
from contracts import *


def classify(a: int, b: int, c: int) -> int:
    Ensures(Result() >= 0)
    if a > 1000:
        if b == a * 3 - 7:
            if c % 13 == 5 and c > b:
                return -1
    return 1
