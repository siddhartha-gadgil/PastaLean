# Seeded: `~` is int-only, so the `str` annotation cannot hold.
def flip(bits: str) -> int:
    return ~bits
