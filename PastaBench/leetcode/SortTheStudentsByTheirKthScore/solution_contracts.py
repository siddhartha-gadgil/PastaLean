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

def sortTheStudents(score: List[List[int]], k: int) -> List[List[int]]:
    Requires(k >= 0)
    Requires(all(k < len(row) for row in score))
    return sorted(score, key=lambda x: -x[k])