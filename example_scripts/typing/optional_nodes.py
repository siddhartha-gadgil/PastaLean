#!/usr/bin/env python3
"""Optional-typed recursive nodes (TreeNode/ListNode), the shape LeetCode tree problems use.

Each function below broke a different part of the `Option` handling: the unwrap used to fire only on
the outermost receiver, and a field *write* through an `Option` produced invalid Lean.
"""

from typing import Optional


class TreeNode:
    def __init__(self, val=0, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right


class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next


# Field read straight off an `Option` receiver.
def depth(root: Optional[TreeNode]) -> int:
    if not root:
        return 0
    return 1 + max(depth(root.left), depth(root.right))


# Chained read: `root.left` is itself `Option TreeNode`, so `.val` needs a SECOND unwrap.
def left_val(root: Optional[TreeNode]) -> int:
    if root is None or root.left is None:
        return 0
    return root.left.val


# Field WRITE through an `Option`: needs unwrap + re-wrap, not a bare record update.
def bump(head: Optional[ListNode]) -> int:
    n = 0
    while head:
        head.val = head.val + 1
        n += 1
        head = head.next
    return n


# Reassigning the Option-typed cursor itself, the standard linked-list walk.
def total(head: Optional[ListNode]) -> int:
    acc = 0
    while head:
        acc += head.val
        head = head.next
    return acc
