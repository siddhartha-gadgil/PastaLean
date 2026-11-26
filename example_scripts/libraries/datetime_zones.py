from datetime import date, datetime, time, timedelta, timezone


def to_utc(dt: datetime) -> datetime:
    return dt.astimezone(timezone.utc)


if __name__ == "__main__":
    ist = timezone(timedelta(hours=5, minutes=30))
    t = datetime(2024, 3, 10, 14, 5, 9, 0, ist)
    print(t, t.isoformat(), to_utc(t), repr(timezone.utc), str(ist), repr(ist))
    print(t - datetime(2024, 3, 10, 8, 0, 0, 0, timezone.utc), t.utcoffset())
    print(datetime.fromisoformat("2024-03-10T14:05:09.250+05:30"), datetime.fromisoformat("2024-01-01T00:00:00Z"))
    lunch = time(12, 30)
    print(lunch, repr(lunch), lunch.isoformat(timespec="minutes"), time(9, 5, 1, 7) < lunch)
    print(datetime.combine(date(2024, 2, 29), lunch), datetime(2024, 2, 29, 23, 59).time())
    print(datetime(1970, 1, 2, tzinfo=timezone.utc).timestamp())
    print(date.today() > date(2020, 1, 1), datetime.now(timezone.utc).year >= 2024)
    try:
        timezone(timedelta(hours=24))
    except ValueError as e:
        print("error:", e)
    naive, aware = datetime(2024, 1, 1), datetime(2024, 1, 1, tzinfo=timezone.utc)
    print(naive == aware, sorted([datetime(2024, 5, 1), naive])[0])
    try:
        print(naive < aware)
    except TypeError as e:
        print("error:", e)
