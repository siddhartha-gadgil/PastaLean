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


def maxNumber(n: int) -> int:
    Requires(n > 0)
    # The result is (1 << (n.bit_length() - 1)) - 1, i.e. the largest number with all lower bits set below the highest bit of n.
    Ensures(Result() == (1 << (n.bit_length() - 1)) - 1)
    return (1 << n.bit_length() - 1) - 1