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

def sumBase(n: int, k: int) -> int:
    Requires(n >= 0)
    Requires(k >= 2)
    Ensures(Result() >= 0)

    ans = 0
    while n:
        Invariant(n >= 0)
        Invariant(ans >= 0)
        Decreases(n)
        ans += n % k
        n //= k
    return ans