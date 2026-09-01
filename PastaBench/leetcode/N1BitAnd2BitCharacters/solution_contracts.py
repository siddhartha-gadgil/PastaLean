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


def isOneBitCharacter(bits: List[int]) -> bool:
    Requires(len(bits) > 0)
    Requires(all(b >= 0 for b in bits))    # bits[i]+1 must be positive for termination
    i, n = 0, len(bits)
    while i < n - 1:
        Invariant(0 <= i)
        Invariant(i < n - 1)               # for safe bits[i] access
        Invariant(i <= n)
        Decreases(n - 1 - i)
        i += bits[i] + 1
    Assert(i == n - 1 or i == n)           # exit position is exactly n-1 or n
    return i == n - 1