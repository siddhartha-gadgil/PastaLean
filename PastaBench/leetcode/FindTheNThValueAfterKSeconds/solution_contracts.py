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

def valueAfterKSeconds(n: int, k: int) -> int:
    Requires(n >= 1)
    Requires(k >= 0)

    a = [1] * n
    mod = 10 ** 9 + 7

    for _ in range(k):
        for i in range(1, n):
            # bounds needed for safe indexing of a and a[i-1]
            Invariant(1 <= i)
            Invariant(i < n)
            a[i] = (a[i] + a[i - 1]) % mod

    return a[n - 1]