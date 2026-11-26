# The regex forgets the sign JSON allows after an exponent (`0e-1`). Every branch involved is covered by
# some input early on (a sign after `e` in `1e-5`, a falsy `0e0`), so coverage alone does not steer to the
# conjunction: the search puts the operand `s[k] == "-"` compared against where `0e0` held its `0`.
import json
import re

FALSEY = re.compile(r'\s*(null|false|""|-?0(\.0+)?([eE][0-9]+)?|\[\s*\]|\{\s*\})\s*')


def is_falsey(s: str) -> bool:
    """
    raises: json.JSONDecodeError
    post: __return__
    """
    return bool(json.loads(s)) or bool(FALSEY.fullmatch(s))
