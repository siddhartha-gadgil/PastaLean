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


def flowerGame(n: int, m: int) -> int:
    Requires(n >= 0)
    Requires(m >= 0)
    # The game pairs flowers across two halves, yielding floor(n*m/2) total cross-pairs
    Ensures(Result() == (n * m) // 2)
    a1 = (n + 1) // 2
    b1 = (m + 1) // 2
    a2 = n // 2
    b2 = m // 2
    res = a1 * b2 + a2 * b1
    # bridge to the postcondition
    Assert(res == (n * m) // 2)
    return res