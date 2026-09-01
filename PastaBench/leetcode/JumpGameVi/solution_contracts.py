import random
import functools
import string
import math
import datetime
from typing import *
from functools import *
from collections import *
from itertools import *
from heapq import *
from bisect import *
from string import *
from operator import *
from math import *
from contracts import *
import collections
from collections import deque
from typing import List


def _naive_maxResult(nums: List[int], k: int) -> int:
    # pure DP spec for correctness
    n = len(nums)
    f2 = [float("-inf")] * n
    f2[0] = nums[0]
    for i in range(1, n):
        # take max of the last k DP values
        lo = i - k if i - k > 0 else 0
        f2[i] = nums[i] + max(f2[lo:i])
    return f2[-1]


def maxResult(nums: List[int], k: int) -> int:
    Requires(len(nums) > 0)
    Requires(k > 0)
    Ensures(Result() == _naive_maxResult(nums, k))    # the point: matches the pure DP spec

    n = len(nums)
    f = [0] * n
    q = deque([0])
    for i in range(n):
        Invariant(0 <= i)
        Invariant(i <= n)
        # q only holds valid indices in the sliding window [max(0, i-k) .. i]
        Invariant(all(0 <= j < n for j in q))
        Invariant(all(max(0, i - k) <= j <= i for j in q))
        Invariant(len(q) > 0)
        # f[q[0]] is the current maximum of f[j] for j in [max(0,i-k) .. i)
        Invariant(all(f[q[0]] >= f[j] for j in range(max(0, i - k), i)))

        if i - q[0] > k:
            q.popleft()
        Assert(all(max(0, i - k) <= j <= i for j in q))

        f[i] = nums[i] + f[q[0]]
        while q and f[q[-1]] <= f[i]:
            q.pop()
        q.append(i)

    return f[-1]