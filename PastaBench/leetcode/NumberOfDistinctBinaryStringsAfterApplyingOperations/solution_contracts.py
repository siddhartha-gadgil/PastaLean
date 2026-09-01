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

def countDistinctStrings(s: str, k: int) -> int:
    Requires(k >= 0)
    Requires(k <= len(s) + 1)
    return pow(2, len(s) - k + 1) % (10 ** 9 + 7)