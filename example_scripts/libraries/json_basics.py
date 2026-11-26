import json


def total(doc: str) -> int:
    data = json.loads(doc)
    s = 0
    for x in data["xs"]:
        s += x
    return s


if __name__ == "__main__":
    d = json.loads('{"name": "pasta", "xs": [1, 2, 3], "nested": {"ok": true}}')
    print(d["name"], d["nested"]["ok"], len(d["xs"]))
    print(total('{"xs": [10, 20, 5]}'))
    print(json.dumps(d, indent=2, sort_keys=True))
    print(json.dumps([1, "a", None]))
    try:
        json.loads("[1, 2")
    except ValueError as e:
        print("error:", e)
