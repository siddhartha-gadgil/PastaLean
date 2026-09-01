import random
import functools
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
import collections
from collections import Counter

def numberOfSubstrings(s: str) -> int:
    # The result counts all substrings whose first and last characters match.
    # Closed‐form: for each distinct c, if occ = s.count(c), then it contributes occ*(occ+1)/2.
    Ensures(2 * Result() == sum(s.count(c) * (s.count(c) + 1) for c in set(s)))
    cnt = Counter()
    ans = 0
    for c in s:
        cnt[c] += 1
        ans += cnt[c]
    return ans