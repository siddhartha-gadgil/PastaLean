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


def rearrangeSticks(n: int, k: int) -> int:
    Requires(n >= 0)
    Requires(k >= 0)
    Requires(k <= n)
    mod = 10 ** 9 + 7
    Ensures(0 <= Result() < mod)
    f = [[0] * (k + 1) for _ in range(n + 1)]
    f[0][0] = 1
    # Build DP table: f[i][j] = number of ways mod m
    for i in range(1, n + 1):
        Invariant(1 <= i)
        Invariant(i <= n)
        for j in range(1, k + 1):
            Invariant(1 <= j)
            Invariant(j <= k)
            Invariant(0 <= f[i-1][j-1] < mod)
            Invariant(0 <= f[i-1][j] < mod)
            f[i][j] = (f[i - 1][j - 1] + f[i - 1][j] * (i - 1)) % mod
            Assert(0 <= f[i][j] < mod)
    Assert(0 <= f[n][k] < mod)
    return f[n][k]