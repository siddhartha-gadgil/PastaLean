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

def minFlips(target: str) -> int:
    Requires(all(c in '01' for c in target))
    ans = 0
    for v in target:
        if ans & 1 ^ int(v):
            ans += 1
    return ans