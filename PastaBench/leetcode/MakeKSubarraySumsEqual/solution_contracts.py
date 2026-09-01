import random
import functools
import collections
import string
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
import math

def makeSubKSumEqual(arr: List[int], k: int) -> int:
    Requires(len(arr) > 0)
    Ensures(Result() >= 0)
    n = len(arr)
    g = math.gcd(n, k)
    ans = 0
    for i in range(g):
        Invariant(0 <= i)
        Invariant(i < g)
        Invariant(ans >= 0)
        t = sorted(arr[i:n:g])
        mid = t[len(t) >> 1]
        ans += sum(abs(x - mid) for x in t)
        Assert(ans >= 0)
    return ans