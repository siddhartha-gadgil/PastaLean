import heapq
import itertools
from sortedcontainers import SortedList
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

class TreeNode:

    def __init__(self, val=0, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right

def pathSum(root: Optional[TreeNode], targetSum: int) -> List[List[int]]:
    Ensures(all(sum(path) == targetSum for path in Result()))
    def dfs(root, s):
        if root is None:
            return
        s += root.val
        t.append(root.val)
        if root.left is None and root.right is None and (s == targetSum):
            Assert(sum(t) == s)
            ans.append(t[:])
        dfs(root.left, s)
        dfs(root.right, s)
        t.pop()
    ans = []
    t = []
    dfs(root, 0)
    return ans