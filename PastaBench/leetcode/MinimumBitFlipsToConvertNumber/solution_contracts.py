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

def minBitFlips(start: int, goal: int) -> int:
    Ensures(Result() == (start ^ goal).bit_count())
    return (start ^ goal).bit_count()