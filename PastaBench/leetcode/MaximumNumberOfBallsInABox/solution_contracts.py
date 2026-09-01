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


def countBalls(lowLimit: int, highLimit: int) -> int:
    Requires(lowLimit >= 1)
    Requires(highLimit >= lowLimit)
    Ensures(Result() >= 1)
    cnt = [0] * 50
    for x in range(lowLimit, highLimit + 1):
        y = 0
        while x:
            y += x % 10
            x //= 10
        Assume(0 <= y < len(cnt))
        cnt[y] += 1
    return max(cnt)