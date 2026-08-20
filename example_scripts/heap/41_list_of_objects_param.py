# A list-of-objects crossing a function boundary with a dotted container annotation (--heap). The
# parameter `nodes: typing.List[Node]` lowers to `Ref (List (Ref Node))`; the dotted `typing.` head
# must be recognised both for the ref-typing AND for populating the `Val` cell universe (a bare-Name
# head is not the only container form). Inside, `nodes[i].val` derefs an element; a write mutates the
# caller's shared objects in place.
import typing


class Node:
    def __init__(self, val: int):
        self.val = val


def first_val(nodes: typing.List[Node]) -> int:
    return nodes[0].val


def total(nodes: typing.List[Node]) -> int:
    s = 0
    for i in range(len(nodes)):
        s += nodes[i].val
    return s


def double_first(nodes: typing.List[Node]) -> None:
    nodes[0].val = nodes[0].val * 2


if __name__ == "__main__":
    a = Node(9)
    b = Node(4)
    xs = [a, b]
    print(first_val(xs))   # 9
    print(total(xs))       # 13
    double_first(xs)       # mutate the caller's first element through the ref
    print(a.val)           # 18 (mutation visible on the caller's object)
    print(total(xs))       # 22
