"""Binary blank-tape TM runner and independent small Laver tables (positive representatives)."""

from dataclasses import dataclass
from pathlib import Path


def load_machine(path):
    states = {}
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        line = line.partition("#")[0].strip()
        if not line:
            continue
        name, on_zero, on_one = line.split()
        if name in states or name == "HALT":
            raise ValueError(name)
        row = []
        for word in (on_zero, on_one):
            if word[0] not in "01" or word[1] not in "LR" or not word[2:]:
                raise ValueError((name, word))
            row.append((int(word[0]), 1 if word[1] == "R" else -1, word[2:]))
        states[name] = tuple(row)
    for row in states.values():
        for _, _, dest in row:
            if dest != "HALT" and dest not in states:
                raise ValueError(dest)
    return states


@dataclass
class Configuration:
    state: str
    head: int
    ones: set[int]
    steps: int = 0

    def advance(self, machine, *, until=(), budget=200_000, radius=20_000):
        for _ in range(budget):
            bit = int(self.head in self.ones)
            write, direction, self.state = machine[self.state][bit]
            if write:
                self.ones.add(self.head)
            else:
                self.ones.discard(self.head)
            self.head += direction
            self.steps += 1
            if abs(self.head) > radius:
                raise RuntimeError("test tape limit")
            if self.state == "HALT" or self.state in until:
                return self
        raise RuntimeError(f"test step limit at {self.state}, head {self.head}")


def laver_table(n):
    if not 0 <= n <= 8:
        raise ValueError("small verification tables only")
    size = 1 << n
    table = [[0] * (size + 1) for _ in range(size + 1)]
    table[size][1:] = range(1, size + 1)
    for a in range(size - 1, 0, -1):
        row = table[a]
        row[1] = a + 1
        for b in range(2, size + 1):
            row[b] = table[row[b - 1]][a + 1]
    return table
