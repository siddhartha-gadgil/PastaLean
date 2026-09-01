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

def isIdealPermutation(nums: List[int]) -> bool:
    # Domain: the algorithm assumes non-negative integers
    Requires(all(isinstance(n, int) and n >= 0 for n in nums))
    # The result is True exactly when no non-local inversion exists:
    # for every i >= 2, the maximum of nums[:i-1] does not exceed nums[i].
    Ensures(Result() == all(max(nums[:j-1], default=0) <= nums[j]
                            for j in range(2, len(nums))))
    mx = 0
    for i in range(2, len(nums)):
        if (mx := max(mx, nums[i - 2])) > nums[i]:
            return False
    return True