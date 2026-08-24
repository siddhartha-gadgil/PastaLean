class Cell:
    def __init__(self, v: int):
        self.v = v

def bump(c: Cell, k: int) -> None:
    i = 0
    while i < k:
        c.v = c.v + 1
        i = i + 1

def main() -> None:
    c = Cell(10)
    bump(c, 3)
    print(c.v)

if __name__ == "__main__":
    main()
