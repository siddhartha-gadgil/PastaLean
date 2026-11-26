from datetime import date, datetime, timedelta


def days_until(start: date, end: date) -> int:
    return (end - start).days


def add_business_days(d: date, n: int) -> date:
    while n > 0:
        d = d + timedelta(days=1)
        if d.weekday() < 5:
            n -= 1
    return d


if __name__ == "__main__":
    a = date(2024, 2, 28)
    b = a + timedelta(days=2)
    print(a, b, b.weekday(), b.isoformat(), repr(b))
    print(days_until(a, date(2025, 1, 1)))
    print(add_business_days(date(2024, 12, 27), 3))
    print(date.fromisoformat("2023-07-04").strftime("%A %d %B %Y, day %j"))
    t = datetime(2024, 3, 10, 14, 5, 9)
    print(t, t + timedelta(hours=12, minutes=55, seconds=51), t.isoformat(timespec="minutes"))
    print(datetime.fromisoformat("2024-03-10T14:05:09.250") - t)
    print(timedelta(days=-1, seconds=30), timedelta(weeks=2) // 3, -timedelta(hours=1))
    print(sorted([date(2024, 5, 1), date(2023, 1, 1), date(2024, 1, 1)])[0], a < b, a == date(2024, 2, 28))
    try:
        date(2023, 2, 29)
    except ValueError as e:
        print("error:", e)
