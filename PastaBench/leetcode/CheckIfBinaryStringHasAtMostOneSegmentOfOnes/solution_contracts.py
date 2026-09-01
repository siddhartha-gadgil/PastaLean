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

def checkOnesSegment(s: str) -> bool:
    Ensures(Result() == ('01' not in s))    # The result is true iff there is no '0'→'1' transition
    return '01' not in s