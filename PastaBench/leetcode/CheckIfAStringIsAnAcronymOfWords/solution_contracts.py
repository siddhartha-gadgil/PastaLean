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

def isAcronym(words: List[str], s: str) -> bool:
    Requires(all(len(w) > 0 for w in words))
    return ''.join((w[0] for w in words)) == s