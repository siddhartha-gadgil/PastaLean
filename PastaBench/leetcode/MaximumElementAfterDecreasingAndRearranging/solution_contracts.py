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

def maximumElementAfterDecrementingAndRearranging(arr: List[int]) -> int:
    Requires(len(arr) > 0)
    arr.sort()
    arr[0] = 1
    for i in range(1, len(arr)):
        Invariant(1 <= i)
        Invariant(i < len(arr))
        d = max(0, arr[i] - arr[i - 1] - 1)
        arr[i] -= d
    return max(arr)