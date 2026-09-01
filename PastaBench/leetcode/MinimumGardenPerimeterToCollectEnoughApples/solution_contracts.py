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


def minimumPerimeter(neededApples: int) -> int:
    Requires(neededApples >= 1)
    x = 1
    # Loop finds the smallest x >= 1 with 2*x*(x+1)*(2*x+1) >= neededApples
    while 2 * x * (x + 1) * (2 * x + 1) < neededApples:
        Invariant(x >= 1)
        Invariant(2 * x * (x + 1) * (2 * x + 1) < neededApples)
        x += 1
    # On exit, the condition is false → we've reached the threshold
    Assert(2 * x * (x + 1) * (2 * x + 1) >= neededApples)
    # And x is minimal: stepping back fails the threshold (unless x==1)
    Assert(x == 1 or 2 * (x - 1) * x * (2 * (x - 1) + 1) < neededApples)
    return x * 8