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

def theMaximumAchievableX(num: int, t: int) -> int:
    Requires(t >= 0)
    Ensures(Result() == num + 2 * t)
    return num + t * 2