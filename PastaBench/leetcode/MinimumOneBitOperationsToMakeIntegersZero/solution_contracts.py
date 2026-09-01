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

def minimumOneBitOperations(n: int) -> int:
    Requires(n >= 0)
    Decreases(n)
    ans = 0
    while n:
        Invariant(n >= 0)
        Invariant(ans >= 0)
        ans ^= n
        n >>= 1
    return ans