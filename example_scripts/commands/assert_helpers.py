from typing import List, Optional


def check_code(code: str) -> bool:
    assert len(code) == 2


def check_codes(codes: List[str]) -> bool:
    if len(codes) == 0:
        raise ValueError("no codes")
    for c in codes:
        check_code(c)


def describe(codes: List[str], fallback: Optional[str]) -> str:
    check_codes(codes)
    if fallback is not None:
        check_code(fallback)
    return ",".join(codes)


def is_short(code: str) -> bool:
    assert len(code) <= 3


def all_short(codes: List[str]) -> bool:
    for c in codes:
        is_short(c)
    return True


if __name__ == "__main__":
    print(describe(["en", "fr"], None))
    print(all_short(["abc", "de"]))
    try:
        check_codes([])
    except ValueError as e:
        print("error:", e)
