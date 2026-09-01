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

def longestSemiRepetitiveSubstring(s: str) -> int:
    Requires(len(s) >= 1)
    Ensures(1 <= Result() <= len(s))
    ans, n = (1, len(s))
    cnt = j = 0
    for i in range(1, n):
        # bounds for indexing and counters
        Invariant(1 <= i < n)
        Invariant(0 <= j <= i)
        Invariant(0 <= cnt <= 1)
        Invariant(1 <= ans <= n)
        cnt += s[i] == s[i - 1]
        # shrink window if too many repeats
        Decreases(n - j)
        while cnt > 1:
            Invariant(0 <= j <= i)
            Invariant(cnt >= 0)
            cnt -= s[j] == s[j + 1]
            j += 1
        # now the window [j..i] has at most one adjacent repeat
        Assert(cnt <= 1)
        ans = max(ans, i - j + 1)
        Assert(ans >= i - j + 1)
    return ans