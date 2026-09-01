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
import itertools

def findPoisonedDuration(timeSeries: List[int], duration: int) -> int:
    Requires(duration >= 0)
    Requires(all(timeSeries[i] < timeSeries[i+1] for i in range(len(timeSeries)-1)))
    Ensures(
        Result()
        == duration
        + sum(
            min(duration, timeSeries[i] - timeSeries[i - 1])
            for i in range(1, len(timeSeries))
        )
    )
    ans = duration
    for a, b in itertools.pairwise(timeSeries):
        ans += min(duration, b - a)
    # Bridge to the postcondition: the accumulated ans matches the closed-form sum of intervals.
    Assert(
        ans
        == duration
        + sum(
            min(duration, timeSeries[i] - timeSeries[i - 1])
            for i in range(1, len(timeSeries))
        )
    )
    return ans