# Iterative linked-list reversal (--heap). Exercises `Optional[C]` threaded through the heap tier
# end-to-end: `reverse` takes and returns `Optional[Node]` (lowered to `Option (Ref Node)`), its
# cursors (`prev`/`curr`/`nxt`) are ref locals whose `.next` read and `.next` write hit the heap via
# `((x).getD default) ~> next`, and in `__main__` the object-returning call `head = reverse(a)`
# registers `head` as a heap ref so the print traversal derefs correctly. Each cursor is
# single-assignment-per-role so its `Option (Ref Node)` type stays unambiguous.
from typing import Optional


class Node:
    def __init__(self, val: int, next=None):
        self.val = val
        self.next = next


def reverse(head: Optional[Node]) -> Optional[Node]:
    prev: Optional[Node] = None
    curr: Optional[Node] = head
    while curr is not None:
        nxt: Optional[Node] = curr.next   # READ through a ref-typed local
        curr.next = prev                  # WRITE through a ref-typed local (mutation hits the heap)
        prev = curr
        curr = nxt
    return prev


if __name__ == "__main__":
    a = Node(1)
    b = Node(2)
    c = Node(3)
    a.next = b
    b.next = c
    head: Optional[Node] = reverse(a)     # returns the new head (c); list is now 3 -> 2 -> 1
    node: Optional[Node] = head
    while node is not None:
        print(node.val)                   # 3, 2, 1
        node = node.next
