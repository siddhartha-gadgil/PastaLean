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

def separateDigits(nums: List[int]) -> List[int]:
    Requires(all(x >= 0 for x in nums))
    Ensures(all(0 <= d < 10 for d in Result()))
    ans = []
    for x in nums:
        Invariant(all(0 <= d < 10 for d in ans))
        Assert(x >= 0)
        t = []
        while x:
            Invariant(x >= 0)
            Invariant(all(0 <= d < 10 for d in t))
            digit = x % 10
            Assert(0 <= digit < 10)
            t.append(digit)
            x //= 10
        ans.extend(t[::-1])
        Assert(all(0 <= d < 10 for d in ans))
    return ans