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
import bisect

def findTheDistanceValue(arr1: list[int], arr2: list[int], d: int) -> int:
    Requires(d >= 0)
    Ensures(0 <= Result() <= len(arr1))
    arr2.sort()
    ans = 0
    for x in arr1:
        Invariant(ans >= 0)
        Invariant(ans <= len(arr1))
        i = bisect.bisect_left(arr2, x - d)
        # bisect_left yields 0 <= i <= len(arr2)
        Assert(0 <= i)
        Assert(i <= len(arr2))
        ans += (i == len(arr2) or arr2[i] > x + d)
    return ans