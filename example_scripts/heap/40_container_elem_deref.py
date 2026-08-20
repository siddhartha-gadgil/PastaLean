# Dereferencing an OBJECT held in a container-of-refs (--heap). `nodes : list[Node]` is a heap cell of
# `List (Ref Node)`, so an element is a `Ref Node`. Reading a field off one derefs through the pointer,
# whether the receiver is a direct Subscript (`nodes[0].val`) or a local bound from one
# (`n = nodes[1]; n.val`). Writing `nodes[0].val = x` mutates the shared object in place. The list
# annotation must also reach the `Val` cell universe so `Storable Val (List (Ref Node))` exists.
from typing import List


class Node:
    def __init__(self, val: int):
        self.val = val


if __name__ == "__main__":
    a = Node(1)
    b = Node(2)
    nodes: List[Node] = [a, b]
    print(nodes[0].val)   # 1  (direct: receiver of .val is a Subscript)
    n = nodes[1]
    print(n.val)          # 2  (bound: n registers as a heap ref from the Subscript RHS)
    nodes[0].val = 10     # WRITE through a Subscript ref receiver
    print(nodes[0].val)   # 10
    print(a.val)          # 10 (mutation visible on the aliased object a)
