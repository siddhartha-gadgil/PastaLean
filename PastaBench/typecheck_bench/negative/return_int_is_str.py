# Seeded: the body returns a `str`, but the signature promises an `int`.
def label(n: int) -> int:
    return "n=" + str(n)
