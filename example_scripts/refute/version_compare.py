# `int()` of a bad literal raises ValueError, which the contract allows; the counterexample needs two
# version strings that compare equal (`"1.0"` and `"1.0"`), which independent draws rarely give.
def compare_versions(version1, version2):
    """
    pre: isinstance(version1, str) and isinstance(version2, str)
    pre: len(version1) == 3 and len(version2) == 3
    raises: ValueError
    post: __return__ != 0
    """
    v1 = version1.split(".")
    v2 = version2.split(".")
    for i in range(max(len(v1), len(v2))):
        a = int(v1[i]) if i < len(v1) else 0
        b = int(v2[i]) if i < len(v2) else 0
        if a > b:
            return 1
        elif a < b:
            return -1
    return 0
