from typing import Iterable, List


def squares(n: int):
    # A generator: `yield` in the body. PastaLean materialises it to a `List Int` (each `yield`
    # becomes an append), so `list(...)`, `sum(...)`, `for`, and comprehensions consume it directly
    # via the `PyIterable` protocol.
    for i in range(n):
        yield i * i


def evens_with_tag(xs: List[int]):
    # Conditional yields plus a trailing yield.
    for x in xs:
        if x % 2 == 0:
            yield x
    yield -1


def chained(a: List[int], b: List[int]):
    # `yield from` delegates to a sub-iterable (extend); mixes with a plain `yield`.
    yield from a
    yield from b
    yield 99


def first_three(n: int):
    # A generator `return` just *stops* iteration — the values yielded so far are the output.
    i = 0
    while i < n:
        yield i
        i += 1
        if i == 3:
            return


def subsets(nums: List[int], start: int):
    # A RECURSIVE generator (backtracking): `yield []` then recurse. The materialised accumulator is
    # typed by TypeInfer (run *after* generator lowering), so `[nums[i]] + tail` stays list-concat —
    # without that the empty-list seed defaults the element type wrong under recursion.
    yield []
    for i in range(start, len(nums)):
        for tail in subsets(nums, i + 1):
            yield [nums[i]] + tail


def evens(xs: List[int]):
    for x in xs:
        if x % 2 == 0:
            yield x


def doubled(xs: Iterable[int]):
    for x in xs:
        yield x * 2


def fib(n: int):
    # Stateful generator: the `a, b = b, a + b` swap threads through the materialised loop.
    a, b = 0, 1
    for _ in range(n):
        yield a
        a, b = b, a + b


def use_generators() -> int:
    a = list(squares(4))           # [0, 1, 4, 9]
    b = list(evens_with_tag([1, 2, 3, 4]))  # [2, 4, -1]
    c = list(chained([1, 2], [3, 4]))       # [1, 2, 3, 4, 99]
    d = [x + 1 for x in squares(3)]         # [1, 2, 5]
    e = list(first_three(10))      # [0, 1, 2]
    f = list(subsets([1, 2, 3], 0))          # 8 subsets
    g = list(doubled(evens([1, 2, 3, 4, 5, 6])))  # [4, 8, 12] — a generator pipeline
    h = list(fib(8))               # [0, 1, 1, 2, 3, 5, 8, 13]
    return sum(a) + len(b) + len(c) + sum(d) + len(e) + len(f) + sum(g) + sum(h)
