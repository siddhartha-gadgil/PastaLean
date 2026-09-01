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


def makePalindrome(s: str) -> bool:
    Ensures(
        # The result is True exactly when there are at most two mismatched symmetric pairs in s
        Result() == (sum(1 for k in range(len(s) // 2) if s[k] != s[len(s) - 1 - k]) <= 2)
    )
    i, j = 0, len(s) - 1
    cnt = 0
    while i < j:
        # Bounds on indices for safe indexing
        Invariant(0 <= i)
        Invariant(i <= len(s))
        Invariant(0 <= j)
        Invariant(j < len(s))
        # The mismatch count is always nonnegative
        Invariant(cnt >= 0)

        cnt += (s[i] != s[j])
        i, j = i + 1, j - 1

    # Bridge: the accumulated count equals the closed‐form sum over floor(len(s)/2) pairs
    Assert(cnt == sum(1 for k in range(len(s) // 2) if s[k] != s[len(s) - 1 - k]))
    return cnt <= 2