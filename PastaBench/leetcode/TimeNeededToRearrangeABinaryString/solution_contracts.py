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

def secondsToRemoveOccurrences(s: str) -> int:
    Ensures(Result() >= 0)
    ans = 0
    while s.count('01'):
        s = s.replace('01', '10')
        ans += 1
    Assert(s.count('01') == 0)
    return ans