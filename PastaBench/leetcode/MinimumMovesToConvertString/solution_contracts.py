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

def minimumMoves(s: str) -> int:
    Ensures(Result() >= 0)
    ans = 0
    i = 0
    # termination measure: remaining length to process
    while i < len(s):
        Invariant(0 <= i)
        Invariant(i <= len(s))
        Invariant(ans >= 0)
        Decreases(len(s) - i)
        if s[i] == 'X':
            ans += 1
            i += 3
        else:
            i += 1
    return ans