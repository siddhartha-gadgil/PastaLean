# Seeded: `chr` takes an `int`, so the `str` annotation is wrong.
def letter(n: str) -> str:
    return chr(n)
