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

def validateStackSequences(pushed: List[int], popped: List[int]) -> bool:
    Requires(len(pushed) == len(popped))
    stk = []
    i = 0
    for x in pushed:
        Invariant(0 <= i)
        Invariant(i <= len(popped))
        stk.append(x)
        while stk and stk[-1] == popped[i]:
            Invariant(len(stk) >= 1)
            Invariant(0 <= i)
            Invariant(i < len(popped))
            Decreases(len(stk))
            stk.pop()
            i += 1
    return i == len(popped)