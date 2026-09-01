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

def waysToDistribute(n: int, k: int) -> int:
    Requires(n >= 0)
    Requires(k >= 0)
    mod = 10 ** 9 + 7
    Ensures(0 <= Result() and Result() < mod)
    f = [[0] * (k + 1) for _ in range(n + 1)]
    f[0][0] = 1
    for i in range(1, n + 1):
        Invariant(1 <= i)
        Invariant(i <= n)
        Decreases(n - i)
        for j in range(1, k + 1):
            Invariant(1 <= j)
            Invariant(j <= k)
            Decreases(k - j)
            f[i][j] = (f[i - 1][j] * j + f[i - 1][j - 1]) % mod
    return f[n][k]