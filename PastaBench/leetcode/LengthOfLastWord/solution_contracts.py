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

def lengthOfLastWord(s: str) -> int:
    # The result is a number of characters, so it's between 0 and len(s).
    Ensures(Result() >= 0)
    Ensures(Result() <= len(s))

    i = len(s) - 1
    # Skip trailing spaces
    while i >= 0 and s[i] == ' ':
        # Bounds for safe indexing
        Invariant(-1 <= i)
        Invariant(i < len(s))
        # Ensures termination
        Decreases(i + 1)
        i -= 1
    # At exit: either we've run off the left, or s[i] is the first non-space from the end
    Assert(i < 0 or s[i] != ' ')

    j = i
    # Find the start of the last word
    while j >= 0 and s[j] != ' ':
        # Bounds for safe indexing and relation to i
        Invariant(-1 <= j)
        Invariant(j <= i)
        Invariant(j < len(s))
        # Ensures termination
        Decreases(j + 1)
        j -= 1
    # At exit: either before start, or s[j] is a space just before the last word
    Assert(j < 0 or s[j] == ' ')

    return i - j