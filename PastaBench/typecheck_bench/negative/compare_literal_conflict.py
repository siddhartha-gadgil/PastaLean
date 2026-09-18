# Seeded: compared against a `str` literal in one branch and shifted in the other.
def classify(v):
    if v == "done":
        return 1
    return v >> 1
