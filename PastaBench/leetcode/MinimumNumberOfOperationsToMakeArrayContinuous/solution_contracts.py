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

def minOperations(nums: List[int]) -> int:
    Ensures(Result() >= 0)
    ans = n = len(nums)
    nums = sorted(set(nums))
    for i, v in enumerate(nums):
        j = bisect_right(nums, v + n - 1)
        ans = min(ans, n - (j - i))
    return ans