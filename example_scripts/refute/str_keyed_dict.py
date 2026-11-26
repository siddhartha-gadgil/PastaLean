# A bare `dict` annotation: TypeInfer reads `dict[str, int]` off the string-keyed accesses, and the
# generator draws dicts keyed by the program's own strings.
def bump(d: dict) -> dict:
    """
    pre: d["age"] < 100
    post: __return__["age"] < 100
    """
    d["age"] += 1
    return d
