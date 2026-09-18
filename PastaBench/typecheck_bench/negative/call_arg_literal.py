# Seeded: the call passes a `str` where the declared parameter is an `int`.
def repeat(word: str, times: int) -> str:
    return word * times


def main():
    print(repeat("ab", "3"))
