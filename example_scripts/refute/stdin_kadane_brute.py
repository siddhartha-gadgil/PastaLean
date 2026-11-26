# The brute-force reference for stdin_kadane_fast.py: every subarray sum.
def main():
    t = int(input())
    for _ in range(t):
        n = int(input())
        a = list(map(int, input().split()))
        best = a[0]
        for i in range(n):
            s = 0
            for j in range(i, n):
                s += a[j]
                best = max(best, s)
        print(best)


if __name__ == "__main__":
    main()
