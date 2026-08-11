# Dereferencing a heap Ref held in a LOCAL (--heap). `nxt = head.next` binds a local of type
# `Option Node`; reading `nxt.val` lowers to a pointer deref `(← ((nxt).getD default) ~> val)` and
# writing `nxt.next = ...` to a heap write `((nxt).getD default) ~> next <~ ...`, NOT a value-mode
# struct rebind. Each cursor is single-assignment so its ref type stays unambiguous (flow-widening a
# reassigned traversal cursor is a separate concern).
class Node:
    def __init__(self, val: int, next=None):
        self.val = val
        self.next = next


def second_val(head: Node) -> int:  # READ through a ref-typed local
    nxt = head.next
    if nxt is not None:
        return nxt.val
    return -1


def link_back(head: Node) -> None:  # WRITE through a ref-typed local (mutation must hit the heap)
    nxt = head.next
    if nxt is not None:
        nxt.next = head


if __name__ == "__main__":
    b = Node(2)
    a = Node(1, b)
    print(second_val(a))   # 2 (read a.next -> b, then b.val through the local)
    print(second_val(b))   # -1 (b.next is None)
    link_back(a)           # b.next = a, written through the local ref
    print(second_val(b))   # 1 (mutation visible: b.next -> a, a.val)
