# A stdin program whose translation is unfaithful: Python dicts iterate in insertion order, PastaLean's
# HashMap does not. `pastalean refute` generates inputs from the reading code and finds e.g. "0 / aa bb".
def main():
    n = int(input())
    words = input().split()
    counts = {}
    for w in words:
        counts[w] = counts.get(w, 0) + 1
    for w in counts:
        print(w, counts[w])


if __name__ == "__main__":
    main()
