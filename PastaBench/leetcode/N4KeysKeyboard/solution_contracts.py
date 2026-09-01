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


def maxA(n: int) -> int:
    Requires(n >= 0)
    dp = list(range(n + 1))
    for i in range(3, n + 1):
        for j in range(2, i - 1):
            dp[i] = max(dp[i], dp[j - 1] * (i - j))
    return dp[-1]