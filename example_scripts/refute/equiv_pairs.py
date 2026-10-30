from contracts import *

# Two implementations, no property written: `pastalean refute equiv_pairs.py --equiv
# count_pairs_brute=count_pairs_fast` checks brute(xs, k) == fast(xs, k) under the brute's Requires.
# The set-based version loses duplicates, so it is wrong on e.g. xs = [0, 0], k = 0.
def count_pairs_brute(xs: list[int], k: int) -> int:
    Requires(k >= 0)
    n = 0
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            if abs(xs[i] - xs[j]) == k:
                n += 1
    return n


def count_pairs_fast(xs: list[int], k: int) -> int:
    seen = set(xs)
    return sum(1 for x in seen if x + k in seen)
