import json
import re

FALSEY = re.compile(
    r"""
\s*
(
    false
  | null
  | ""
  | \-? 0 (\.0+)? ([eE] [\-\+]? [0-9]+)?
  | \{ \s* \}
  | \[ \s* \]
)
\s*
""",
    re.VERBOSE,
)
DATE = re.compile(r"(?P<year>\d{4})-(\d\d)-(\d\d)")


def is_falsey(s: str) -> bool:
    return bool(FALSEY.fullmatch(s))


def agrees(s: str) -> bool:
    try:
        return bool(json.loads(s)) != is_falsey(s)
    except json.JSONDecodeError:
        return True


if __name__ == "__main__":
    for s in ["false", " [ ] ", "-0.00e+5", "{}", "0", "null", "1", '""', "0.5", "[0]"]:
        print(repr(s), is_falsey(s), agrees(s))
    m = DATE.search("due 2024-03-10, paid 2024-04-01")
    if m:
        print(m.group(0), m.group(1), m.groups(), m.span())
    print(DATE.findall("2024-03-10 and 1999-12-31"), re.findall(r"\d+", "a1b22c333"))
    print(re.sub(r"(\w+)=(\d+)", r"\2:\1", "x=1, y=22"), re.split(r"[,;]\s*", "a, b;c"))
    print(bool(re.match(r"hello", "HeLLo world", re.IGNORECASE)), re.fullmatch(r"a.*?c", "abcbc") is None)
    price = re.search(r"(?<=\$)\d+(?:\.\d\d)?(?!\d)", "cost: $42.50 total")
    if price:
        print(price.group(0), float(price.group(0)) * 2)
    opt = re.match(r"(\w+)(?:-(\w+))?", "alpha")
    if opt:
        print(opt.group(1), opt.group(2), opt.group(2) is None, opt.groups(), "<" + opt.group(1) + ">")
    print(bool(re.fullmatch(r"(?i)hello\s+(?#greeting)world", "HELLO   World")), re.findall(r"\b\w+(?=ing\b)", "singing and dancing"))
    print(re.sub(r"(?P<w>\w+)@(?P=w)", r"[\g<w>]", "a@a b@c x@x"), int(re.match(r"\d+", "123abc").group(0)) + 1)
