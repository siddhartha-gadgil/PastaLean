# Seeded: `p` is both `ord`'d (⇒ str) and `chr`'d (⇒ int).
def both(p):
    a = ord(p)
    b = chr(p)
    return a + b
