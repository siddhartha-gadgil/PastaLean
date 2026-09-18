"""`for i in range(len(xs))` proves every `xs[i]` in range, so those reads lower to the
proof-carrying `pyListGetProof` instead of the defaulting `pyGetItem`. Each function below is a
shape the refinement must either take (the first three) or correctly refuse (the rest)."""


def total(xs: list[int]) -> int:
    s = 0
    for i in range(len(xs)):
        s = s + xs[i]
    return s


def pairwise_max(xs: list[int]) -> int:
    best = 0
    for i in range(len(xs)):
        # A second, non-refinable read of the same list in the same body: `i + 1` is not the loop
        # variable, so it keeps the defaulting lowering while `xs[i]` gets the proof.
        if xs[i] > best:
            best = xs[i]
    return best


def grid_sum(g: list[list[int]]) -> int:
    s = 0
    for i in range(len(g)):
        row = g[i]
        for j in range(len(row)):
            s = s + row[j]
    return s


def grow_while_reading(xs: list[int]) -> int:
    # `xs` grows inside the loop, so `len(xs)` at entry bounds nothing.
    s = 0
    for i in range(len(xs)):
        s = s + xs[i]
        xs.append(s)
    return s


def store_through_index(xs: list[int]) -> list[int]:
    # An indexed STORE also invalidates the refinement's reasoning about `xs`.
    for i in range(len(xs)):
        xs[i] = xs[i] * 2
    return xs


def shifted_reads(xs: list[int]) -> int:
    # `i + 1` and `len(xs) - 1 - i` are not the loop variable; both stay defaulting.
    s = 0
    for i in range(len(xs) - 1):
        s = s + xs[i + 1]
    return s


def shadowed_index(xs: list[int]) -> int:
    s = 0
    for i in range(len(xs)):
        f = lambda i: i * 2
        s = s + f(xs[i])
    return s


def aliased_len(xs: list[int]) -> int:
    # `n = len(xs)` once, then `range(n)`: the bound is still `xs`'s length, proved through the alias.
    n = len(xs)
    s = 0
    for i in range(n):
        s = s + xs[i]
    return s


def rebound_alias(xs: list[int]) -> int:
    # `n` is reassigned, so it is no longer a stable alias for `len(xs)`.
    n = len(xs)
    s = 0
    n = n - 1
    for i in range(n):
        s = s + xs[i]
    return s


def main():
    data = [3, 1, 4, 1, 5]
    print(total(data))
    print(pairwise_max(data))
    print(grid_sum([[1, 2], [3, 4, 5]]))
    print(grow_while_reading([1, 2]))
    print(store_through_index([1, 2, 3]))
    print(shifted_reads(data))
    print(shadowed_index(data))
    print(aliased_len(data))
    print(rebound_alias(data))


if __name__ == "__main__":
    main()
