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

def findChampion(n: int, edges: List[List[int]]) -> int:
    Requires(n >= 0)
    Requires(all(0 <= v < n for _, v in edges))
    indeg = [0] * n
    for _, v in edges:
        indeg[v] += 1
    return -1 if indeg.count(0) != 1 else indeg.index(0)