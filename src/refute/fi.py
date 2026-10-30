"""Enclosures of IEEE-754 double results, over exact `Fraction`s.

The executable twin of `PastaLean/PyAPI/FloatInterval.lean`: an `FI` is a closed interval (an end may be
infinite) that contains the double a computation produces. Each operation takes the exact interval of its
result and widens each end by the round-to-nearest bound `err z = max(2⁻⁵³·|z|, 2⁻¹⁰⁷⁵)`; the Lean file
proves that widening sound (`roundEnds_sound`, `add_sound`, `sub_sound`, `neg_sound`).

Passed in place of a float argument (with the module lifted by `lift.py`, so every float it creates is an
`FI` too), arithmetic with ints and other `FI`s works, and a comparison is decided when the enclosures are
ordered — otherwise it raises `RoundingSensitive`, because the outcome then depends on how the hardware
rounds. Anything not modelled raises `Unmodelled`.
"""

from __future__ import annotations

import math
from fractions import Fraction

U = Fraction(1, 2 ** 53)
ETA = Fraction(1, 2 ** 1075)
MAX_FINITE = Fraction((2 ** 53 - 1) * 2 ** 971)
EXACT_INT = 2 ** 53


class RoundingSensitive(ArithmeticError):
    """A comparison whose outcome depends on rounding: the enclosures overlap."""


class Unmodelled(ArithmeticError):
    """A float produced outside the enclosure model (an unmodelled operation or library)."""


#: How many enclosures exist; a caller compares it before and after to see whether a run used any.
created = 0


def _cmp(v):
    """A comparison operand: an enclosure, or ±∞ kept as the float itself."""
    return v if isinstance(v, float) and math.isinf(v) else FI.of(v)


def err(z: Fraction) -> Fraction:
    return max(U * abs(z), ETA)


def lower_end(a):
    if a is None:
        return None
    w = a - err(a)
    return None if w < -MAX_FINITE else w


def upper_end(b):
    if b is None:
        return None
    w = b + err(b)
    return None if w > MAX_FINITE else w


class FI:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        global created
        created += 1
        self.lo, self.hi = lo, hi

    @staticmethod
    def point(q) -> FI:
        q = Fraction(q)
        return FI(q, q)

    @staticmethod
    def of(v) -> FI:
        """An operand as an enclosure: ints beyond 2⁵³ round on conversion to float. A plain float did not
        come through the model, so it has no sound enclosure."""
        if isinstance(v, FI):
            return v
        if isinstance(v, bool):
            return FI.point(int(v))
        if isinstance(v, int):
            q = Fraction(v)
            return FI.point(q) if abs(v) <= EXACT_INT else FI(lower_end(q), upper_end(q))
        if isinstance(v, float):
            raise Unmodelled("a float computed outside the enclosure model")
        raise TypeError(f"no enclosure for {type(v).__name__}")

    @staticmethod
    def rounded(lo, hi) -> FI:
        return FI(lower_end(lo), upper_end(hi))

    # -- arithmetic --------------------------------------------------------------------------------

    def __neg__(self):
        return FI(None if self.hi is None else -self.hi, None if self.lo is None else -self.lo)

    def __pos__(self):
        return self

    def __abs__(self):
        if self.lo is not None and self.lo >= 0:
            return self
        if self.hi is not None and self.hi <= 0:
            return -self
        top = None if self.lo is None or self.hi is None else max(-self.lo, self.hi)
        return FI(Fraction(0), top)

    def __add__(self, other):
        o = FI.of(other)
        lo = None if self.lo is None or o.lo is None else self.lo + o.lo
        hi = None if self.hi is None or o.hi is None else self.hi + o.hi
        return FI.rounded(lo, hi)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-FI.of(other))

    def __rsub__(self, other):
        return FI.of(other) + (-self)

    def __mul__(self, other):
        o = FI.of(other)
        if None in (self.lo, self.hi, o.lo, o.hi):
            return FI(None, None)
        ps = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return FI.rounded(min(ps), max(ps))

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = FI.of(other)
        if o.lo == o.hi == 0:
            raise ZeroDivisionError("float division by zero")
        if o.lo is None or o.hi is None or o.lo <= 0 <= o.hi:
            # Whether Python raises depends on the divisor rounding to exactly zero.
            raise RoundingSensitive("divisor enclosure contains zero")
        if self.lo is None or self.hi is None:
            return FI(None, None)
        qs = [self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi]
        return FI.rounded(min(qs), max(qs))

    def __rtruediv__(self, other):
        return FI.of(other) / self

    # -- comparison: decided only when the enclosures are ordered -----------------------------------

    def _lt(self, o):
        """`True` / `False` when decided, else raise."""
        if isinstance(o, float):
            # ±∞: a finite end (never past the largest double) proves the value finite.
            if o < 0:
                return False
            if self.hi is not None:
                return True
            raise RoundingSensitive("comparison with ∞ depends on overflow")
        if isinstance(self, float):
            if self > 0:
                return False
            if o.lo is not None:
                return True
            raise RoundingSensitive("comparison with ∞ depends on overflow")
        if self.hi is not None and o.lo is not None and self.hi < o.lo:
            return True
        if self.lo is not None and o.hi is not None and self.lo >= o.hi:
            return False
        raise RoundingSensitive("comparison depends on rounding")

    def __lt__(self, other):
        return FI._lt(self, _cmp(other))

    def __gt__(self, other):
        return FI._lt(_cmp(other), self)

    def __le__(self, other):
        return not FI._lt(_cmp(other), self)

    def __ge__(self, other):
        return not FI._lt(self, _cmp(other))

    def __eq__(self, other):
        if isinstance(other, float) and math.isinf(other):
            if (other > 0 and self.hi is not None) or (other < 0 and self.lo is not None):
                return False
            raise RoundingSensitive("equality with ∞ depends on overflow")
        try:
            o = FI.of(other)
        except TypeError:
            return NotImplemented
        if self.lo is not None and self.lo == self.hi == o.lo == o.hi:
            return True
        if (self.hi is not None and o.lo is not None and self.hi < o.lo) or \
                (o.hi is not None and self.lo is not None and o.hi < self.lo):
            return False
        raise RoundingSensitive("equality depends on rounding")

    def __ne__(self, other):
        r = self.__eq__(other)
        return r if r is NotImplemented else not r

    def __bool__(self):
        return self != 0

    def __float__(self):
        # Only library code converts implicitly (`float(x)` itself is lifted): outside the model.
        raise Unmodelled("an enclosure passed to code outside the model")

    def __hash__(self):
        raise Unmodelled("hashing an enclosure (float set/dict key)")

    def contains(self, v: float) -> bool:
        q = Fraction(v)
        return (self.lo is None or self.lo <= q) and (self.hi is None or q <= self.hi)

    def width_ulps(self) -> float | None:
        """The enclosure's width in units of the last place at its centre; `None` when unbounded."""
        if self.lo is None or self.hi is None:
            return None
        c = abs((self.lo + self.hi) / 2)
        ulp = max(c * 2 * U, Fraction(1, 2 ** 1074))
        return float(min((self.hi - self.lo) / ulp, Fraction(10) ** 300))

    def __repr__(self):
        f = lambda e: "inf" if e is None else repr(float(e))  # noqa: E731
        return f"[{f(self.lo) if self.lo is not None else '-inf'}, {f(self.hi)}]"


def enclose(v, t):
    """A value with every float (per its type tree from `harness.parse_type`) replaced by its enclosure."""
    tag = t[0]
    if tag == "float" and isinstance(v, (int, float)) and not isinstance(v, bool):
        return FI.point(Fraction(v))
    if tag == "list" and isinstance(v, list):
        return [enclose(x, t[1]) for x in v]
    if tag == "tuple" and isinstance(v, tuple):
        return tuple(enclose(x, s) for x, s in zip(v, t[1]))
    if tag == "opt" and v is not None:
        return enclose(v, t[1])
    return v

