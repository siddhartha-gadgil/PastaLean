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

def maxJump(stones: List[int]) -> int:
    Requires(len(stones) >= 2)
    ans = stones[1] - stones[0]
    for i in range(2, len(stones)):
        Invariant(2 <= i)
        Invariant(i < len(stones))
        ans = max(ans, stones[i] - stones[i - 2])
    return ans