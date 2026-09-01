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

def minOperations(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() == (n >> 1) * (n - (n >> 1)))
    return sum((n - (i << 1 | 1) for i in range(n >> 1)))