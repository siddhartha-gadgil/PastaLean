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

def longestString(x: int, y: int, z: int) -> int:
    Ensures(
        (x < y and Result() == (x * 2 + z + 1) * 2)
        or (x > y and Result() == (y * 2 + z + 1) * 2)
        or (x == y and Result() == (x + y + z) * 2)
    )
    if x < y:
        return (x * 2 + z + 1) * 2
    if x > y:
        return (y * 2 + z + 1) * 2
    return (x + y + z) * 2