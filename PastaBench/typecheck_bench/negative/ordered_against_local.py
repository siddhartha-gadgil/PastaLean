# Seeded: `i` is an `int`, and Python 3 refuses to order an `int` against a `str`.
def countdown(n: str) -> int:
    i = 0
    while i <= n:
        i = i + 1
    return i
