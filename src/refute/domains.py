"""Value domains for the CPython side (the float report's value sampling; refute itself never searches
in Python): `type_of_hint` turns a resolved annotation into the harness's type tree, with `date`,
`datetime`, `timedelta`, `union` and `any`, and the date/time generators draw those values."""

from __future__ import annotations

import ast
import datetime as dt
import random
import re
import string
import types
import typing

def type_of_hint(tp, depth: int = 0):
    """The harness type tree for a runtime annotation."""
    if depth > 6:
        return ("any",)
    origin, args = typing.get_origin(tp), typing.get_args(tp)
    if tp is type(None) or tp is None:
        return ("none",)
    if tp in (int, float, str, bool):
        return (tp.__name__,)
    if tp is dt.datetime:
        return ("datetime",)
    if tp is dt.date:
        return ("date",)
    if tp is dt.timedelta:
        return ("timedelta",)
    if tp is typing.Any or tp is object:
        return ("any",)
    if origin in (typing.Union, types.UnionType):
        members = [type_of_hint(a, depth + 1) for a in args]
        if ("none",) in members and len(members) == 2:
            return ("opt", next(m for m in members if m != ("none",)))
        return ("union", members)
    if origin in (list, typing.List) or tp is list:
        return ("list", type_of_hint(args[0], depth + 1) if args else ("any",))
    if origin in (set, frozenset) or tp in (set, frozenset):
        return ("set", type_of_hint(args[0], depth + 1) if args else ("any",))
    if origin is dict or tp is dict:
        return ("dict", type_of_hint(args[0], depth + 1) if args else ("key",),
                type_of_hint(args[1], depth + 1) if len(args) > 1 else ("any",))
    if origin is tuple:
        return ("tuple", [type_of_hint(a, depth + 1) for a in args if a is not Ellipsis])
    if isinstance(tp, type):
        return ("obj", tp)
    return ("any",)


def gen_date(rng: random.Random, mined=None) -> dt.date:
    years = [y for y in (mined.ints if mined else []) if 1 <= y <= 9999]
    r = rng.random()
    if years and r < 0.3:
        y = rng.choice(years)
    elif r < 0.5:
        y = rng.choice([1, 2000, 1900, 2024, 9999, 2023])
    else:
        y = rng.randint(1, 9999)
    m = rng.randint(1, 12)
    last = (dt.date(y + (m == 12), m % 12 + 1, 1) - dt.timedelta(days=1)).day if y < 9999 or m < 12 else 31
    d = rng.choice([1, last, rng.randint(1, last)])
    return dt.date(y, m, d)


def gen_timedelta(rng: random.Random, mined, size: int) -> dt.timedelta:
    ints = mined.ints if mined else []
    r = rng.random()
    if ints and r < 0.25:
        days = rng.choice(ints)
    elif r < 0.6:
        days = rng.randint(-size * 40, size * 40)
    else:
        days = rng.randint(-3_000_000, 3_000_000)
    days = max(-999_999_999, min(999_999_999, days))
    secs = rng.choice([0, 0, rng.randint(0, 86399)])
    return dt.timedelta(days=days, seconds=secs)


def gen_datetime(rng: random.Random, mined=None) -> dt.datetime:
    d = gen_date(rng, mined)
    return dt.datetime(d.year, d.month, d.day, rng.choice([0, rng.randint(0, 23)]),
                       rng.choice([0, rng.randint(0, 59)]), rng.choice([0, rng.randint(0, 59)]))

