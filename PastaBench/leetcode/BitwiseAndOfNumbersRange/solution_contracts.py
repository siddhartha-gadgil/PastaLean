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

def rangeBitwiseAnd(left: int, right: int) -> int:
    Requires(0 <= left <= right)
    Ensures(0 <= Result() <= left)
    while left < right:
        Invariant(0 <= left)
        Invariant(left <= right)
        Invariant(0 <= right)
        Invariant(right - left >= 1)
        Decreases(right - left)
        right &= right - 1
    Assert(right <= left)
    return right