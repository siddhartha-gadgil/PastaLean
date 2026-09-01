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

def checkIfPangram(sentence: str) -> bool:
    Ensures(Result() == (len(set(sentence)) == 26))
    return len(set(sentence)) == 26