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

def sumScores(s: str) -> int:
    n = len(s)
    Ensures(sum(z) + n == Result())    # the result is the prefix-match total: n + sum of the Z-array
    z = [0] * n
    l = 0
    r = 0
    for i in range(1, n):
        Invariant(1 <= i)
        Invariant(i < n)
        Invariant(0 <= l)
        Invariant(l < i)           # needed for z[i-l] indexing
        Invariant(0 <= r)
        Invariant(r <= n)
        Invariant(l <= r)
        Invariant(0 <= z[i])
        Invariant(z[i] <= n - i)   # so i+z[i] <= n, making s[z[i]] and s[i+z[i]] safe
        Decreases(n - i)
        if i < r:
            z[i] = min(r - i, z[i - l])
        while i + z[i] < n and s[z[i]] == s[i + z[i]]:
            z[i] += 1
        if i + z[i] > r:
            l = i
            r = i + z[i]
    Assert(sum(z) + n == Result())
    return sum(z) + n