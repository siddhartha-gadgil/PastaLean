from contracts import *


# README's false postcondition: it holds only for an arithmetic progression missing one term, which
# the two preconditions do not say. The refuter finds an input like [2, 0, 2].
def missingNumber(arr: list[int]) -> int:
    Requires(len(arr) >= 1)
    Requires((arr[-1] - arr[0]) % len(arr) == 0)
    Ensures(min(arr[0], arr[-1]) <= Result() <= max(arr[0], arr[-1]))
    return (arr[0] + arr[-1]) * (len(arr) + 1) // 2 - sum(arr)
