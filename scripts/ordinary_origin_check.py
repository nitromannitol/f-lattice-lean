"""Task 43: the lower-left site Q of the raw ordinary standard assembly, and the check P = raw - Q.

Inputs (scripts/data/):
  ordinary_origin_raw.log  from scripts/ordinary_origin_probe.lean: for each ordinary tile of a word of length <= 3,
      `TILE <word> <parity> Q x y SIZE n` then the raw sites `S x y` (raw = union of the six placed copies).
  ordinary_tile_dump.log   from scripts/ordinary_tile_probe.lean (task 42): the native register tile after the word
      (llCenter of the output), `W` / `T odd|even` headers, then `S x y h`.
Claims checked:
  1. Q = (0,0) for every ordinary tile (the raw lower-left site is the origin).
  2. For words whose native register comes from the schedule, the native tile P equals raw - Q as a site set.
  3. The exceptions are the pure two-runs, whose register comes from BaseRun.twos (splitInitial), not from the schedule.
"""
import re
from pathlib import Path

DATA = Path(__file__).parent / "data"
DIG = {"one": 1, "two": 2, "three": 3}


def parse_probe(path):
    tiles = {}
    key = None
    for line in path.read_text().splitlines():
        if line.startswith("TILE "):
            w = tuple(DIG[d] for d in re.findall(r"Digit\.(one|two|three)", line))
            par = re.search(r"Parity\.(odd|even)", line).group(1)
            q = re.search(r" Q (-?\d+) (-?\d+) ", line)
            key = (w, par)
            tiles[key] = {"Q": (int(q.group(1)), int(q.group(2))), "S": set()}
        elif line.startswith("S ") and key:
            _, x, y = line.split()
            tiles[key]["S"].add((int(x), int(y)))
    return tiles


def parse_dump(path):
    dump = {}
    cur, tag = None, None
    for line in path.read_text().splitlines():
        if line.startswith("W "):
            cur = tuple(DIG[d] for d in re.findall(r"Digit\.(one|two|three)", line))
            tag = None
        elif line.startswith("T "):
            tag = line.split()[1]
            dump[(cur, tag)] = set()
        elif line.startswith("S ") and tag:
            _, x, y, _ = line.split()
            dump[(cur, tag)].add((int(x), int(y)))
    return dump


def main():
    tiles = parse_probe(DATA / "ordinary_origin_raw.log")
    dump = parse_dump(DATA / "ordinary_tile_dump.log")
    nonzero = [(w, p, t["Q"]) for (w, p), t in tiles.items() if t["Q"] != (0, 0)]
    print(f"ordinary tiles {len(tiles)}; Q = (0,0) for {len(tiles) - len(nonzero)}; nonzero: {nonzero}")
    match, exceptions = 0, []
    for (w, p), t in tiles.items():
        qx, qy = t["Q"]
        shifted = {(x - qx, y - qy) for (x, y) in t["S"]}
        native = dump.get((w, p))
        if native == shifted:
            match += 1
        else:
            exceptions.append((w, p, len(native or ()), len(shifted)))
    print(f"native tile = raw - Q: {match}; exceptions (native size, raw size): {exceptions}")


if __name__ == "__main__":
    main()
