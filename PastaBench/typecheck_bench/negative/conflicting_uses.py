# Seeded: no annotation, but the two uses demand `str` and `int` at once.
def mangle(token):
    if token.isdigit():
        return ~token
    return 0
