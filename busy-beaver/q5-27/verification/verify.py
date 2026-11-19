"""Replay the printed, named and merged 27-state machines and the bounded tests."""

import json
from pathlib import Path
import re

from bounded_checks import bounded_machine_tests, certified_quotient, finite_tests
from check_machine import load_machine


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def check_transition_tables(machine, merged, start):
    if len(machine) != 27 or next(iter(machine)) != start or set(merged) != set(machine):
        raise ValueError("Unexpected working states or initial state")
    numbers = {state: index for index, state in enumerate(machine, 1)}
    numbers["HALT"] = 0
    expected = []
    for state, edges in machine.items():
        row = [str(numbers[state])]
        for bit, (symbol, direction, target) in enumerate(edges):
            named = f"{symbol}{'R' if direction == 1 else 'L'}{target}"
            certified = merged[state][bit]
            if certified == ".":
                certified = f"{bit}RHALT"
            if named != certified:
                raise ValueError(f"State {state} on {bit}: quotient gives {certified}, table gives {named}")
            row.append(f"{symbol}{'→' if direction == 1 else '←'}{numbers[target]}")
        expected.append(row)

    table = (ROOT / "transitions.txt").read_text(encoding="utf-8").splitlines()
    if [line.split() for line in table if line.strip()] != expected:
        raise ValueError("The numerical table differs from the simulator table")
    for filename in ("proof.md", "proof.zh-CN.md"):
        paper = (ROOT / filename).read_text(encoding="utf-8")
        tables = re.findall(r"^~~~text\n(.*?)^~~~", paper, re.MULTILINE | re.DOTALL)
        matches = [[line.split() for line in block.splitlines() if line.strip()] == expected for block in tables]
        if sum(matches) != 1:
            raise ValueError(f"Expected exactly one copy of the same table in {filename}")


def main():
    if not __debug__:
        raise SystemExit("Run without -O so the bounded proof checks remain enabled.")
    source = json.loads((HERE / "source-machine.json").read_text(encoding="utf-8"))
    groups = json.loads((HERE / "state-groups.json").read_text(encoding="utf-8"))
    raw, start = source["rows"], source["start"]
    merged, names = certified_quotient(raw, groups)
    machine = load_machine(ROOT / "machine.tm")
    check_transition_tables(machine, merged, names[start])

    cells, below, unshifted = finite_tests()
    config = dict(source["config"], reverse=True, zero_guard=True)
    checks = bounded_machine_tests(raw, start, config, machine, names)
    assert (cells, below) == (86_368, 42_439)
    assert (checks["states"], checks["raw_copies"], checks["centre"]) == (27, 912, 5)
    assert checks["products"][0] == [549, 636] and checks["restarts"] == 7
    assert checks["blank"] == [(12, 300), (24, 2_630)]
    assert (3, 8, 126_983, 11) in checks["seeded_successes"]
    print(json.dumps({
        "working_states": len(machine),
        "transitions_checked": 2 * len(machine),
        "unmerged_states": len(raw),
        "forward_table_checks": cells,
        "q_less_than_p": below,
        "unshifted_disagreements": unshifted,
        "machine_checks": checks,
    }, indent=2))


if __name__ == "__main__":
    main()
