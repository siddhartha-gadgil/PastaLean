# Seeded: `name` is annotated `str` but shifted, which is int-only in Python.
def scramble(name: str) -> int:
    return name << 2
