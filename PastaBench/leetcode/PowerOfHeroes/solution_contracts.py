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

def sumOfPower(nums: List[int]) -> int:
    Ensures(0 <= Result() < 10**9+7)
    mod = 10**9 + 7
    nums.sort()
    ans = 0
    p = 0
    for x in nums[::-1]:
        Invariant(0 <= ans)
        Invariant(ans < 10**9+7)
        ans = (ans + x * x % mod * x) % mod
        ans = (ans + x * p) % mod
        p = (p * 2 + x * x) % mod
    return ans