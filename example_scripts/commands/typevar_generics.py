# `T = TypeVar("T")` generics are translated at the dynamic type; icontract-style contract decorators
# are specifications and are not translated.
from typing import Dict, List, Sequence, Tuple, TypeVar

from icontract import require

T = TypeVar("T")


def pairs(x: List[T]) -> List[Tuple[T, T]]:
    return [(x[i], x[i + 1]) for i in range(len(x) - 1)]


@require(lambda s: len(s) > 0)
def to_dict(s: Sequence[T]) -> Dict[T, T]:
    return dict(zip(s, s))


def main():
    print(len(pairs([1, 2, 3])), len(to_dict([1, 1, 2])))


if __name__ == "__main__":
    main()
