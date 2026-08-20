# Chained field dereference through heap refs (--heap). `a.next` is itself a ref-typed field read, so
# `a.next.val` dereferences TWICE: the receiver of the final `.val` is an Attribute (not a bare Name),
# and `a.next.next` chains a third hop. Recognising each receiver as a heap ref keys off its inferred
# type, not the syntactic form — a bare-Name-only rule would emit value-mode `.val` on a `Ref`.
from typing import Optional


class Node:
    def __init__(self, val: int, next=None):
        self.val = val
        self.next = next


if __name__ == "__main__":
    c = Node(3)
    b = Node(2, c)
    a = Node(1, b)
    print(a.val)             # 1
    print(a.next.val)        # 2  (one hop: receiver of .val is the Attribute a.next)
    print(a.next.next.val)   # 3  (two hops chained)
    a.next.val = 20          # WRITE through a chained (Attribute) ref receiver
    print(a.next.val)        # 20 (mutation visible on the shared ref b)
    print(b.val)             # 20
