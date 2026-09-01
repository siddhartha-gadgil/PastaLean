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

def queryString(s: str, n: int) -> bool:
    Requires(n >= 0)
    if n > 1000:
        return False
    Assert(n <= 1000)
    return all((bin(i)[2:] in s for i in range(n, n // 2, -1)))