# type: ignore
"""Annotations that are WRONG as Python typing but common in real (LeetCode) code. PastaLean must
still translate them; the `# type: ignore` header marks the file unchecked, so type-checking
benchmarks skip it.
"""

from typing import List

inf = float("inf")


class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next


# Param annotated as a bare `ListNode` (NOT `Optional`), but `head = head.next` makes it nullable —
# inference must widen the cursor to `Option ListNode` and the run twin must suffix the param class.
def get_decimal(head: ListNode) -> int:
    ans = 0
    while head:
        ans = ans << 1 | head.val
        head = head.next
    return ans


# `-> int` DPs whose `inf` sentinel makes the value `int | float`; they return an `int` whenever the
# target is reachable, which is what CPython prints.
def inf_dp(cost: List[int]) -> int:
    # Canonical `[inf]*n` DP: `inf` adapts to the container's float type across both twins.
    n = len(cost)
    dp = [inf] * (n + 1)
    dp[0] = 0
    for i in range(1, n + 1):
        dp[i] = min(dp[i - 1] + cost[i - 1], dp[i])
    return dp[n]


def grid_inf_dp(houses: List[int]) -> int:
    # A 2-D `[[inf]*k for _ in …]` DP: the comprehension is a nested list-container seeded by the
    # polymorphic `inf`, so it must be ascribed the twin's float type (`List (List ℚ)` / `Float`) —
    # otherwise `inf` defaults to ℚ while the run twin's values are `Float` (a `PySetItem (List ℚ) ℤ
    # Float` clash). Mirrors the allocate-mailboxes shape.
    n = len(houses)
    f = [[inf] * (n + 1) for _ in range(n)]
    for i in range(n):
        f[i][1] = houses[i]
        for j in range(2, i + 2):
            for p in range(i):
                f[i][j] = min(f[i][j], f[p][j - 1] + houses[i])
    return f[n - 1][n]


def dp_sentinel_return(cost: List[int]) -> int:
    # The canonical inf-DP ending: `return -1 if unreachable else value`. The single ternary return
    # mixes `int` (`-1`) with the `float` DP value, so both branches are elaborated at the mode float
    # (`ℚ`/`Float`) — the `-1` coerces up (int→ℚ / int→Float) instead of pinning the result to `ℤ`.
    n = len(cost)
    dp = [inf] * (n + 1)
    dp[0] = 0
    for i in range(1, n + 1):
        dp[i] = min(dp[i - 1] + cost[i - 1], dp[i])
    return -1 if dp[n] >= inf else dp[n]


def coin_change(coins: list[int], amount: int) -> int:
    inf = float('inf')
    m, n = len(coins), amount
    f = [[inf] * (n + 1) for _ in range(m + 1)]
    f[0][0] = 0
    for i, x in enumerate(coins, 1):
        for j in range(n + 1):
            f[i][j] = f[i - 1][j]
            if j >= x:
                f[i][j] = min(f[i][j], f[i][j - x] + 1)
    return -1 if f[m][n] >= inf else f[m][n]


def main():
    print(inf_dp([3, 1, 4]))
    print(grid_inf_dp([1, 4, 8, 10, 20]))
    print(dp_sentinel_return([2, 7, 1]))
    print(coin_change([1, 2, 5], 11))        # 3  (5+5+1)
    print(coin_change([2], 3))               # -1


if __name__ == "__main__":
    main()
