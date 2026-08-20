# A METHOD that returns a heap ref, bound to a local, then dereferenced (--heap). The declared return
# type (`-> Leaf`) types the call `o.get_leaf()` as `Ref Leaf`, so the bound local `got` registers as
# a heap object and `got.v` derefs through the pointer. Free-function `_ref_class`/`_heap_call` stamps
# guard on a Name callee, so the method path is a distinct case. Two classes (Leaf before Owner) avoid
# a forward reference, isolating the method-return-ref behaviour.
class Leaf:
    def __init__(self, v: int):
        self.v = v


class Owner:
    def __init__(self, leaf: Leaf):
        self.leaf = leaf

    def get_leaf(self) -> Leaf:
        return self.leaf

    def bump(self, k: int) -> None:
        self.leaf.v += k


if __name__ == "__main__":
    it = Leaf(7)
    o = Owner(it)
    got = o.get_leaf()
    print(got.v)          # 7 (deref a method-returned ref bound to a local)
    o.bump(5)             # mutate the shared leaf through the owner
    print(got.v)          # 12 (got and o.leaf alias the same heap cell)
    print(o.get_leaf().v) # 12 (deref a method-returned ref directly, no local)
