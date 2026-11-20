# `x or default` on an Optional takes the payload type (None is falsy): in a constructor's field
# initialiser and in a plain function.
from typing import List, Optional, Tuple


class Cart:
    def __init__(self, items: Optional[List[Tuple[str, int]]] = None):
        self.items = items or []


def count(xs: Optional[List[int]]) -> int:
    ys = xs or [0]
    return len(ys)


def main():
    print(len(Cart().items), len(Cart([("a", 1)]).items), count(None), count([1, 2]), count([5]))


if __name__ == "__main__":
    main()
