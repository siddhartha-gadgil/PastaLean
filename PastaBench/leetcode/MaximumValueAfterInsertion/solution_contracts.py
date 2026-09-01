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


def maxValue(n: str, x: int) -> str:
    Requires(0 <= x)
    Requires(x <= 9)
    Ensures(len(Result()) == len(n) + 1)
    i = 0
    if n[0] == '-':
        i += 1
        # Bound and termination for the negative branch loop
        while i < len(n) and int(n[i]) <= x:
            Invariant(0 <= i)
            Invariant(i <= len(n))
            Decreases(len(n) - i)
            i += 1
    else:
        # Bound and termination for the non-negative branch loop
        while i < len(n) and int(n[i]) >= x:
            Invariant(0 <= i)
            Invariant(i <= len(n))
            Decreases(len(n) - i)
            i += 1
    # Ensure the insertion index is within the valid slice range
    Assert(0 <= i)
    Assert(i <= len(n))
    return n[:i] + str(x) + n[i:]