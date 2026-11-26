# Assumes a dict iterates in sorted key order; it iterates in insertion order.
def first_key(d: dict[int, int]) -> int:
    for k in d:
        return k
    return 0


def smallest_key(d: dict[int, int]) -> int:
    return min(d) if d else 0


def first_is_smallest(d: dict[int, int]):
    assert first_key(d) == smallest_key(d)
