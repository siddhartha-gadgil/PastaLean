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

def buildArray(target: List[int], n: int) -> List[str]:
    Requires(all(1 <= x <= n for x in target))
    Requires(all(target[i] < target[i+1] for i in range(len(target)-1)))
    ans = []
    cur = 1
    for x in target:
        while cur < x:
            ans.extend(['Push', 'Pop'])
            cur += 1
        ans.append('Push')
        cur += 1
    return ans