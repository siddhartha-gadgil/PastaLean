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

def isSameAfterReversals(num: int) -> bool:
    Requires(num >= 0)
    Ensures(Result() == (num == 0 or num % 10 != 0))
    return num == 0 or num % 10 != 0