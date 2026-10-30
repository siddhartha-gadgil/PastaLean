# Brute force is obviously correct; the "optimized" Kadane seeds `best` with 0, so it is wrong on an
# all-negative list. The property function states they agree; the refuter finds e.g. xs = [-1].
def max_sub_brute(xs: list[int]) -> int:
    best = xs[0]
    for i in range(len(xs)):
        s = 0
        for j in range(i, len(xs)):
            s += xs[j]
            best = max(best, s)
    return best


def max_sub_fast(xs: list[int]) -> int:
    best = 0
    cur = 0
    for x in xs:
        cur = max(x, cur + x)
        best = max(best, cur)
    return best


def agree(xs: list[int]):
    if len(xs) >= 1:
        assert max_sub_brute(xs) == max_sub_fast(xs)
