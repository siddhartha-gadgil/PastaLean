# The regex forgets JSON's `0.0`: the search expands the pattern's members (`0`, `-0`, `0e5`, …) and
# edits them with the pattern's own characters until one parses as JSON but does not match.
import json
import re

FALSEY = re.compile(r"\s*(null|false|0|-0|\[\s*\]|\{\s*\})\s*")


def is_falsey(s: str) -> bool:
    """
    raises: json.JSONDecodeError
    post: __return__
    """
    return bool(json.loads(s)) or bool(FALSEY.fullmatch(s))
