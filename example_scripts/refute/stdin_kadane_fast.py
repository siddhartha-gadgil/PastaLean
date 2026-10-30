# Kadane seeded with 0, reading test cases from stdin: wrong when every element is negative.
# `pastalean refute stdin_kadane_fast.py --against stdin_kadane_brute.py --negative` finds "1 / 1 / -1".
def main():
    t = int(input())
    for _ in range(t):
        n = int(input())
        a = list(map(int, input().split()))
        best = 0
        cur = 0
        for x in a:
            cur = max(x, cur + x)
            best = max(best, cur)
        print(best)


if __name__ == "__main__":
    main()
