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

def maximumBeauty(nums: List[int], k: int) -> int:
    Requires(len(nums) > 0)
    Requires(k >= 0)
    Requires(min(nums) >= 0)
    m = max(nums) + 2 * k + 2
    d = [0] * m
    for x in nums:
        Invariant(0 <= x)
        Invariant(x + 2 * k + 1 < m)
        d[x] += 1
        d[x + 2 * k + 1] -= 1
    return max(accumulate(d))