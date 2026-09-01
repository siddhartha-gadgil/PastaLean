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


def numWaterBottles(numBottles: int, numExchange: int) -> int:
    Requires(numBottles >= 0)
    Requires(numExchange > 1)
    orig = numBottles
    Ensures(Result() == orig + (orig - 1) // (numExchange - 1))
    ans = numBottles
    while numBottles >= numExchange:
        Invariant(orig >= numBottles)
        Invariant(numBottles >= 0)
        Invariant((numExchange - 1) * (ans - orig) == orig - numBottles)
        Decreases(numBottles)
        numBottles -= numExchange - 1
        ans += 1
    return ans