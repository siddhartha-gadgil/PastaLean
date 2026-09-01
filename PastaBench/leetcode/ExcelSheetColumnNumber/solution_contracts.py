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

def titleToNumber(columnTitle: str) -> int:
    Requires(all('A' <= ch <= 'Z' for ch in columnTitle))
    ans = 0
    for c in map(ord, columnTitle):
        Assert(ord('A') <= c <= ord('Z'))
        ans = ans * 26 + c - ord('A') + 1
    return ans