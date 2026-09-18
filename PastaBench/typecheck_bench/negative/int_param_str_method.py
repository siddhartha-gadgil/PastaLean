# Seeded: `code` is annotated `int` but `.isalpha()` exists only on `str`.
def is_word(code: int) -> bool:
    return code.isalpha()
