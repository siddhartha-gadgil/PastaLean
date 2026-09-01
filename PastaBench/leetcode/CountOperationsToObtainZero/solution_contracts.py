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


def countOperations(num1: int, num2: int) -> int:
    Requires(num1 >= 0 and num2 >= 0)
    ans = 0
    while num1 and num2:
        Invariant(num1 >= 0)
        Invariant(num2 >= 0)
        Invariant(ans >= 0)
        Invariant(num1 + num2 > 0)
        Decreases(num1 + num2)
        if num1 >= num2:
            num1 -= num2
        else:
            num2 -= num1
        ans += 1
    return ans