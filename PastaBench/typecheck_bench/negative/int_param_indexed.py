# Seeded: a number has no indexing or iteration, so the `int` annotation is wrong.
def first_two(xs: int) -> int:
    total = 0
    for x in xs:
        total += x
    return total + xs[0]
