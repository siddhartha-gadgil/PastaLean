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

def doesAliceWin(s: str) -> bool:
    Ensures(Result() == any(c in 'aeiou' for c in s))
    vowels = set('aeiou')
    return any((c in vowels for c in s))