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

def smallestEvenMultiple(n: int) -> int:
    Ensures((n % 2 == 0 and Result() == n)
            or (n % 2 != 0 and Result() == 2 * n))
    return n if n % 2 == 0 else n * 2