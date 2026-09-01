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

def furthestDistanceFromOrigin(moves: str) -> int:
    Ensures(Result() == abs(moves.count('L') - moves.count('R')) + moves.count('_'))
    return abs(moves.count('L') - moves.count('R')) + moves.count('_')