import random
import functools
import collections
import string
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
import math
from typing import List

def constructRectangle(area: int) -> List[int]:
    Requires(area >= 1)
    Ensures(Result()[0] * Result()[1] == area)
    w = int(math.sqrt(area))
    while area % w != 0:
        w -= 1
    Assert(area % w == 0)
    return [area // w, w]