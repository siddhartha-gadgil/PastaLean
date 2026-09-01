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

def orderlyQueue(s: str, k: int) -> str:
    orig = s
    Requires(k >= 1)
    # The result is the lexicographically smallest rotation if k == 1,
    # otherwise it is the fully sorted string.
    Ensures(
        (k == 1
         and any(Result() == orig[i:] + orig[:i] for i in range(len(orig)))
         and all(Result() <= orig[i:] + orig[:i] for i in range(len(orig))))
        or (k > 1 and Result() == ''.join(sorted(orig)))
    )
    if k == 1:
        ans = s
        for _ in range(len(s) - 1):
            s = s[1:] + s[0]
            ans = min(ans, s)
        # Bridge: ans is a rotation of the original string and is minimal among them
        Assert(any(ans == orig[i:] + orig[:i] for i in range(len(orig))))
        Assert(all(ans <= orig[i:] + orig[:i] for i in range(len(orig))))
        return ans
    return ''.join(sorted(s))