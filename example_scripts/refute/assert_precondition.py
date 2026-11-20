from typing import List, Optional
from icontract import require, ensure

# The precondition is a chain of assertion helpers (`-> bool` but no `return`), over a class that extends
# another and a field `Optional[List[Sub]]`: the search must generate valid objects, which needs the
# assertions evaluated as raises, as CPython does.


class Label:
    def __init__(self, lang: str, text: str):
        self.lang = lang
        self.text = text


class ShortLabel(Label):
    pass


class Entry:
    def __init__(self, labels: List[ShortLabel], alias: Optional[List[ShortLabel]], code: Optional[str]):
        self.labels = labels
        self.alias = alias
        self.code = code


def check_label(that: Label) -> bool:
    assert len(that.lang) == 2, "a two-letter language code"


def check_entry(e: Entry) -> bool:
    assert len(e.labels) >= 1
    for label in e.labels:
        check_label(label)
    if e.alias is not None:
        assert len(e.alias) >= 1
    if e.code is not None:
        assert len(e.code) >= 1


def is_entry(e: Entry) -> bool:
    check_entry(e)
    return True


@require(lambda e: is_entry(e))
@ensure(lambda result: len(result) >= 4)
def headline(e: Entry) -> str:
    return e.labels[0].lang + ":" + e.labels[0].text
