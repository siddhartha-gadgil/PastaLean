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
  
def maximumScore(a: int, b: int, c: int) -> int:
    Requires(a >= 0 and b >= 0 and c >= 0)
    Ensures(Result() >= 0)
    Ensures(2 * Result() <= a + b + c)

    s = sorted([a, b, c])
    ans = 0
    S0 = a + b + c
    while s[1]:
        Invariant(len(s) == 3)
        Invariant(s[0] >= 0)
        Invariant(s[1] >= 0)
        Invariant(s[2] >= 0)
        Invariant(ans >= 0)
        Invariant(s[0] + s[1] + s[2] + 2 * ans == S0)
        Decreases(s[0] + s[1] + s[2])

        ans += 1
        s[1] -= 1
        s[2] -= 1
        s.sort()
    return ans