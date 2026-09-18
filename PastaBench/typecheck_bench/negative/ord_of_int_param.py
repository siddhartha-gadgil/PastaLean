# Seeded: `ord` takes a one-character `str`, so the `int` annotation is wrong.
def code_point(ch: int) -> int:
    return ord(ch)
