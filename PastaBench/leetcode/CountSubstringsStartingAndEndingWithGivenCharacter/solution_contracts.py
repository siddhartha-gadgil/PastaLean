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

def countSubstrings(s: str, c: str) -> int:
    Requires(len(c) > 0)
    # The number of substrings of s that start and end with c is k + (k choose 2),
    # i.e. k*(k+1)/2 where k = s.count(c).
    Ensures(2 * Result() == s.count(c) * (s.count(c) + 1))
    cnt = s.count(c)
    return cnt + cnt * (cnt - 1) // 2