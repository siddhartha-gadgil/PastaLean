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
from typing import List

def numberOfWeeks(milestones: List[int]) -> int:
    Requires(len(milestones) > 0)
    Ensures(
        Result()
        == (
            sum(milestones)
            if max(milestones) <= (sum(milestones) - max(milestones)) + 1
            else 2 * (sum(milestones) - max(milestones)) + 1
        )
    )
    mx, s = max(milestones), sum(milestones)
    rest = s - mx
    # Bridge facts so the Ensures clause (in terms of sum/max) can be rewritten to locals
    Assert(mx == max(milestones))
    Assert(s == sum(milestones))
    return rest * 2 + 1 if mx > rest + 1 else s