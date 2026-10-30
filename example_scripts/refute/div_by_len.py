# CPython raises ZeroDivisionError on `[]`, and so does the runnable twin; the provable twin's total model
# has `x // 0 = 0`, so the theorem holds (and is provable) although the program crashes there.
def mean_floor(xs: list[int]) -> int:
    return sum(xs) // len(xs)


def mean_bound(xs: list[int]):
    assert mean_floor(xs) * len(xs) <= sum(xs)
