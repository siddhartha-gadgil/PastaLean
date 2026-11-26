from datetime import date, timedelta


if __name__ == "__main__":
    big = timedelta(days=999999999)
    print(big, abs(-big), -timedelta(days=3, hours=1), timedelta(weeks=2) // 3, timedelta(hours=1) * 3)
    try:
        print(timedelta(days=10**9))
    except OverflowError as e:
        print("ctor OverflowError:", e)
    try:
        print(big + timedelta(days=1))
    except OverflowError as e:
        print("add OverflowError:", e)
    try:
        print(big * 2)
    except OverflowError as e:
        print("mul OverflowError:", e)
    try:
        print(-(big + timedelta(hours=1) - timedelta(hours=1) + timedelta(seconds=1)))
    except OverflowError as e:
        print("neg OverflowError:", e)
    try:
        print(date(9999, 12, 31) + timedelta(days=1))
    except OverflowError as e:
        print("date OverflowError:", e)
