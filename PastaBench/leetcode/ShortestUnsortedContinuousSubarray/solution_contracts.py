import random
import functools
import collections
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
from typing import List

def findUnsortedSubarray(nums: List[int]) -> int:
    Ensures(Result() >= 0)
    Ensures(Result() <= len(nums))
    n = len(nums)
    arr = sorted(nums)
    l, r = 0, n - 1

    # advance l past the sorted prefix
    while l <= r and nums[l] == arr[l]:
        Invariant(0 <= l)
        Invariant(l <= n)
        Decreases(n - l)
        l += 1
    Assert(0 <= l <= n)

    # retreat r past the sorted suffix
    while l <= r and nums[r] == arr[r]:
        Invariant(0 <= r)
        Invariant(r < n)
        Invariant(r >= -1)
        Decreases(r - (-1))
        r -= 1
    Assert(-1 <= r < n)

    result = r - l + 1
    return result