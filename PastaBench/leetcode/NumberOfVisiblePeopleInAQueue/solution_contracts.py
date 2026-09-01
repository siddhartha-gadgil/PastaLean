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

def canSeePersonsCount(heights: List[int]) -> List[int]:
    Ensures(len(Result()) == len(heights))
    n = len(heights)
    ans = [0] * n
    stk: List[int] = []
    for i in range(n - 1, -1, -1):
        Invariant(0 <= i)
        Invariant(i < len(ans))
        # Pop all shorter people to the right
        while stk and stk[-1] < heights[i]:
            ans[i] += 1
            stk.pop()
        # If there's still someone taller or equal, count them too
        if stk:
            ans[i] += 1
        stk.append(heights[i])
    return ans