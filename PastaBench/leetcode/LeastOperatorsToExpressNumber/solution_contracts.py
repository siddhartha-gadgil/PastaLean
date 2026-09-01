import random
from contracts import *
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

def leastOpsExpressTarget(x: int, target: int) -> int:
    Requires(x >= 2)
    Requires(target >= 1)

    @cache
    def dfs(v: int) -> int:
        if x >= v:
            return min(v * 2 - 1, 2 * (x - v))
        k = 2
        while x ** k < v:
            k += 1
        if x ** k - v < v:
            return min(k + dfs(x ** k - v),
                       k - 1 + dfs(v - x ** (k - 1)))
        return k - 1 + dfs(v - x ** (k - 1))

    return dfs(target)