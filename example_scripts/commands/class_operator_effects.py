from typing import Optional, overload


class Money:
    """Amounts in cents; arithmetic validates, mirroring datetime's overloaded `-`."""

    def __init__(self, cents: int, currency: str = "EUR"):
        if cents < -10**9:
            raise ValueError(f"amount too small: {cents!r}")
        self.cents = cents
        self.currency = currency

    @classmethod
    def parse(cls, text: str) -> "Money":
        whole, frac = text.split(".")
        return Money(int(whole) * 100 + int(frac))

    def __add__(self, other: "Money") -> "Money":
        if self.currency != other.currency:
            raise ValueError("currency mismatch")
        return Money(self.cents + other.cents, self.currency)

    @overload
    def __sub__(self, other: "Money") -> "Money": ...

    @overload
    def __sub__(self, other: int) -> "Money": ...

    def __sub__(self, other):
        if isinstance(other, int):
            return Money(self.cents - other, self.currency)
        return Money(self.cents - other.cents, self.currency)

    def __neg__(self) -> "Money":
        return Money(-self.cents, self.currency)

    def __lt__(self, other: "Money") -> bool:
        return self.cents < other.cents

    def __eq__(self, other: "Money") -> bool:
        return self.cents == other.cents and self.currency == other.currency

    def __bool__(self) -> bool:
        return self.cents != 0

    def __str__(self) -> str:
        return f"{self.cents // 100}.{self.cents % 100:02d} {self.currency}"

    def __repr__(self) -> str:
        return f"Money({self.cents}, {self.currency!r})"


def total(prices: list[Money], discount: Optional[int] = None) -> Money:
    acc = Money(0)
    for p in prices:
        acc = acc + p
    if discount is not None:
        acc = acc - discount
    return acc


if __name__ == "__main__":
    a = Money.parse("12.50")
    b = Money(375)
    print(a + b, a - b, a - 50, -b, repr(a))
    print(total([a, b, Money(5)]), total([a], discount=250))
    print(sorted([a, b, Money(1)]), a < b, a == Money(1250), bool(Money(0)), Money(0) is True)
    try:
        print(a + Money(1, "USD"))
    except ValueError as e:
        print("error:", e)
    try:
        Money(-10**10)
    except ValueError as e:
        print("error:", e)
