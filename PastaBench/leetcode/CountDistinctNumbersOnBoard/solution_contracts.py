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

def distinctIntegers(n: int) -> int:
    Ensures(Result() >= 1)
    return max(1, n - 1)