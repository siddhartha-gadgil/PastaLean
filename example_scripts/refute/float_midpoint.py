# A float bug that is not a rounding effect: `a + b / 2` is not the midpoint. The IEEE enclosure decides
# the violation for every rounding-consistent result, so the refutation holds in floats robustly.
def midpoint(a: float, b: float) -> float:
    return a + b / 2


def midpoint_between(a: float, b: float):
    m = midpoint(a, b)
    assert min(a, b) <= m <= max(a, b)
