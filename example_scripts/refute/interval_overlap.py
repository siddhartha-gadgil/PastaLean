# Closed intervals overlap when they share a point; the "fast" test uses < and misses intervals that
# only touch at an endpoint, e.g. Interval(0, 0) and Interval(0, 0).
class Interval:
    def __init__(self, lo: int, hi: int):
        self.lo = lo
        self.hi = hi


def overlap_brute(a: Interval, b: Interval) -> bool:
    for x in range(min(a.lo, b.lo), max(a.hi, b.hi) + 1):
        if a.lo <= x <= a.hi and b.lo <= x <= b.hi:
            return True
    return False


def overlap_fast(a: Interval, b: Interval) -> bool:
    return a.lo < b.hi and b.lo < a.hi


def overlap_agree(a: Interval, b: Interval):
    assert overlap_brute(a, b) == overlap_fast(a, b)
