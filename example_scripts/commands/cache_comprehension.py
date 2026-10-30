# A `@cache` DP whose recursion sits inside a list comprehension: the runnable twin memoizes it
# via a monadic `mapM` over the shared `StateM` cache (turning exponential into polynomial).
from functools import cache
from typing import List


def max_score(nums: List[int]) -> int:
    n = len(nums)

    @cache
    def dfs(i: int) -> int:
        if i >= n - 1:
            return 0
        return max([(j - i) * nums[j] + dfs(j) for j in range(i + 1, n)] + [0])

    return dfs(0)


def main():
    print(max_score([1, 5, 8, 2, 9]))


if __name__ == "__main__":
    main()
