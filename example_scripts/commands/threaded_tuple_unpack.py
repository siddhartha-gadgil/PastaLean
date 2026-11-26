# A nested def that MUTATES a captured var (`vis`, so it is state-threaded) AND returns a TUPLE, whose
# result is TUPLE-UNPACKED (`a, b = dfs(i)`) inside a `for` loop. The threaded call rewrites to
# `((a, b), vis) = dfs'(i, vis)` — a NESTED tuple target in a `do` block — which nests null-node
# wrappers; the do-sequence flattener must recurse or the inner wrapper leaks as a stray `null`.
def count_components(n: int, adj: list[list[int]]) -> int:
    vis = [False] * n

    def dfs(i: int) -> tuple[int, int]:
        vis[i] = True
        nodes, edges = (1, len(adj[i]))
        for j in adj[i]:
            if not vis[j]:
                a, b = dfs(j)
                nodes += a
                edges += b
        return (nodes, edges)

    complete = 0
    for i in range(n):
        if not vis[i]:
            v, e = dfs(i)
            if e == v * (v - 1):
                complete += 1
    return complete


def main():
    # two triangles (complete) + one path of 2 (complete) → 3 complete components
    print(count_components(8, [[1, 2], [0, 2], [0, 1], [4, 5], [3, 5], [3, 4], [7], [6]]))
    print(count_components(3, [[1], [0], []]))


if __name__ == "__main__":
    main()
