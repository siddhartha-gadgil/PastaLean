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

def poorPigs(buckets: int, minutesToDie: int, minutesToTest: int) -> int:
    Requires(buckets >= 1)
    Requires(minutesToDie > 0)
    Requires(minutesToTest >= minutesToDie)

    base = minutesToTest // minutesToDie + 1
    Ensures(base ** Result() >= buckets)

    res, p = 0, 1
    while p < buckets:
        Invariant(0 <= res)
        Invariant(p == base ** res)
        Invariant(p < buckets)
        Decreases(buckets - p)

        p *= base
        res += 1

    Assert(base ** res >= buckets)
    return res