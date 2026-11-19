"""Bounded probes for the IBLP -> ordinary Laver-table lower-bound problem.

This is NOT a proof of a BMS lower bound.  It implements the unmarked BLP
Copied / fullcomp / M operations from Notes on Laver Tables, version 5,
Definitions 2.12, 2.20 and 2.22.  In particular M completes the original
eligible rows in decreasing order, unlike some interactive BLP programs.

Original IBLP is imported read-only.  Its implicit endpoint i+1 is restored
before viewing a pattern as an ordinary BLP.  Erasing marks or changing the
expansion rule is only an experiment, not an asserted simulation.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import importlib.util
import sys
import time


SOURCE = Path(__file__).resolve().parents[2] / "laver_table_lower_bounds/code/iblp_original.py"


class BudgetExceeded(BaseException):
    pass


@dataclass
class Budget:
    deadline: float
    max_rows: int = 2000
    max_entries: int = 200_000

    def check(self, p: "BLP") -> None:
        if time.monotonic() >= self.deadline:
            raise BudgetExceeded("time limit")
        if len(p.rows) > self.max_rows:
            raise BudgetExceeded("row limit")
        if sum(map(len, p.rows)) > self.max_entries:
            raise BudgetExceeded("entry limit")


@dataclass(frozen=True)
class BLP:
    rows: tuple[tuple[int, ...], ...]
    steps: tuple[int, ...]

    def validate(self) -> None:
        assert len(self.rows) == len(self.steps) >= 2
        assert self.rows[:2] == ((0, 1, 2), (0, 1, 2, 3))
        assert self.steps[:2] == (1, 1)
        for i, (row, step) in enumerate(zip(self.rows, self.steps), 1):
            assert tuple(sorted(set(row))) == row
            assert row[-2:] == (i, i + 1)
            size = len(row)
            if size % 2:
                assert step == (size - 1) // 2
            elif size == 4:
                assert step == 1
            else:
                assert size > 4 and step in (size // 2, size // 2 - 1)

    def kind(self) -> str:
        if len(self.rows) == 2:
            return "zero"
        top = self.rows[-1]
        if top[:3] == (0, 1, 2):
            if len(top) == 5:
                return "successor"
            if len(top) == 6 and self.steps[-1] == 3:
                return "limit"
        return "transient"

    def primitive_sequence(self) -> tuple[int, ...] | None:
        """Recognize exactly the canonical p_alpha family below epsilon_0."""
        out = []
        for i, (row, step) in enumerate(zip(self.rows[2:], self.steps[2:]), 3):
            if step == 2 and row == (0, 1, 2, i, i + 1):
                out.append(0)
            elif step == 3 and len(row) == 6 and row[:3] == (0, 1, 2):
                out.append(row[3] - 2)
            else:
                return None
        return tuple(out)

    def show(self) -> str:
        return " ".join(f"{row}:{step}" for row, step in zip(self.rows, self.steps))


def copied(p: BLP, budget: Budget) -> BLP | None:
    budget.check(p)
    if len(p.rows) == 2:
        return None
    n, top, step = len(p.rows), p.rows[-1], p.steps[-1]
    a, e = top[-step - 2], top[-step - 1]
    if a == 0:
        return None
    mapping = {x: top[k + step] for k, x in enumerate(top[:-step])}
    rows, steps = list(p.rows[:-1]), list(p.steps[:-1])
    for src in range(a, e):
        new = []
        for x in p.rows[src - 1]:
            if x > e:
                return None
            if x < top[0]:
                new.append(x)
            elif x >= a:
                new.append(n + x - a)
            elif x in mapping:
                new.append(mapping[x])
            else:
                return None
        rows.append(tuple(new))
        steps.append(p.steps[src - 1])
    q = BLP(tuple(rows), tuple(steps))
    budget.check(q)
    q.validate()
    return q


def fullcomp(p: BLP, i: int, budget: Budget) -> BLP:
    budget.check(p)
    row, step = p.rows[i - 1], p.steps[i - 1]
    assert len(row) == 2 * step + 1
    low, cur = row[step - 1], row[step]
    points = []
    while True:
        nxt = p.rows[cur - 1][-3]
        assert nxt < cur
        if nxt <= low:
            break
        points.append(nxt)
        cur = nxt
    points.reverse()
    u = len(points)
    if not u:
        return p
    if len(p.rows) + u > budget.max_rows:
        raise BudgetExceeded("completion row limit")
    rows, steps = list(p.rows[:i - 1]), list(p.steps[:i - 1])
    for r in range(u):
        rows.append(tuple(sorted(row[:-1] + tuple(points[:r + 1])
                                 + tuple(range(i + 1, i + r + 2)))))
        steps.append(step + r + 1)
    rows.append(tuple(sorted(row[:-1] + tuple(points)
                             + tuple(range(i + 1, i + u + 2)))))
    steps.append(step + u)
    for old, old_step in zip(p.rows[i:], p.steps[i:]):
        rows.append(tuple(x + u if x > i else x for x in old))
        steps.append(old_step)
    q = BLP(tuple(rows), tuple(steps))
    budget.check(q)
    q.validate()
    return q


def modify(p: BLP, budget: Budget) -> BLP | None:
    q = copied(p, budget)
    if q is None:
        return None
    suitable = [i for i, row in enumerate(q.rows, 1)
                if len(row) > 3 and len(row) % 2 == 1]
    for i in reversed(suitable):
        q = fullcomp(q, i, budget)
    return q


def load_iblp():
    spec = importlib.util.spec_from_file_location("iblp_original", SOURCE)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def restore_endpoints(p) -> BLP:
    result = BLP(tuple(tuple(row) + (i + 1,)
                       for i, row in enumerate(p.rows[1:], 1)), tuple(p.rows[0]))
    result.validate()
    return result


def check_small_cap_family(iblp, root, budget: Budget) -> None:
    """Check the closed formula used in the fixed-generator cap obstruction."""
    p = iblp._apply_number(root, 0, silent=True)[0]
    for r in range(1, 41):
        child = iblp._apply_number(p, r + 1, silent=True)[0]
        expected = [[0, 1], [0, 1, 2]]
        for k in range(1, r + 1):
            expected.extend(([2*k, 2*k+1], [2*k, 2*k+1, 2*k+2]))
        assert child.rows[1:] == expected
        assert child.rows[0] == [1] * (2*r + 2)
        assert not any(child.mask)
        q = restore_endpoints(child)
        budget.check(q)
        trace = set().union(*map(set, q.rows))  # All steps are 1.
        assert trace == set(range(2*r + 4))
    print("CAP_FAMILY: 40 exact original-IBLP checks passed")


def check_seed_completion(iblp, root, budget: Budget) -> None:
    """Check that A[n]'s scan is a sequence of ordinary BLP completions.

    The indices of inserted points here are only syntax.  The proof that
    they denote elementary-embedding images is in the accompanying note.
    """
    for n in range(2, 33):
        raw = root.clone()
        for _ in range(n - 1):
            raw = iblp._copy_full(raw)
        raw.cut()
        expected = [[0, 1], [0, 1, 2], [0, 1, 2, 3]]
        expected += [[0, 1, r - 1, r] for r in range(4, n + 3)]
        assert raw.rows[1:] == expected
        assert raw.rows[0] == [1, 1, 2] + [2] * (n - 1)
        assert not any(raw.mask)
        q = restore_endpoints(raw)
        r = 4
        while r <= len(q.rows):
            # Every original row encountered has the suitable five-point form.
            assert len(q.rows[r - 1]) == 5 and q.steps[r - 1] == 2
            old_size = len(q.rows)
            q = fullcomp(q, r, budget)
            r += len(q.rows) - old_size + 1
        actual = iblp._apply_number(root, n, silent=True)[0]
        assert q == restore_endpoints(actual)
        assert len(q.rows) == 2 + n * (n + 1) // 2
    print("SEED_COMPLETION: n=2..32 match ordinary BLP completion exactly (marks forgotten)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=20)
    parser.add_argument("--max-seed", type=int, default=5)
    parser.add_argument("--max-transient-steps", type=int, default=80)
    args = parser.parse_args()
    assert 0 < args.seconds <= 40
    assert 0 <= args.max_seed <= 12
    assert 0 <= args.max_transient_steps <= 200
    budget = Budget(time.monotonic() + args.seconds)
    iblp = load_iblp()
    root = iblp.reconstruct_pattern_list([0, 1], silent=True)[1][-1]
    print("IBLP root A =", root.to_string())
    check_small_cap_family(iblp, root, budget)
    check_seed_completion(iblp, root, budget)

    p = restore_endpoints(root)
    expected = [
        BLP(((0,1,2),(0,1,2,3),(0,1,2,3,4),(0,1,2,3,4,5),
             (0,1,2,3,4,5,6)), (1,1,2,3,3)),
        BLP(((0,1,2),(0,1,2,3),(0,1,2,3,4),(0,1,2,3,4,5),
             (3,4,5,6)), (1,1,2,3,1)),
        BLP(((0,1,2),(0,1,2,3),(0,1,2,3,4),(0,1,2,3,4,5),
             (0,1,2,4,5,6)), (1,1,2,3,3)),
    ]
    for k, target in enumerate(expected, 1):
        p = modify(p, budget)
        assert p == target
        print(f"A -> M^{k}:", p.show())
    assert p.primitive_sequence() == (0, 1, 2)
    print("EXACT: restored unmarked A becomes p_(omega^omega) after 3 M steps")

    for n in range(args.max_seed + 1):
        seed = iblp._apply_number(root, n, silent=True)[0]
        p = restore_endpoints(seed)
        for k in range(args.max_transient_steps + 1):
            budget.check(p)
            if p.kind() != "transient":
                print(f"A[{n}]: M_steps={k}, rows={len(p.rows)}, type={p.kind()}, "
                      f"primitive={p.primitive_sequence()}, top={p.rows[-1]}:{p.steps[-1]}")
                break
            if k == args.max_transient_steps:
                print(f"A[{n}]: UNKNOWN transient-step limit, rows={len(p.rows)}")
                break
            q = modify(p, budget)
            if q is None:
                print(f"A[{n}]: noncopyable transient after {k} M steps")
                break
            p = q


if __name__ == "__main__":
    try:
        main()
    except BudgetExceeded as exc:
        print("UNKNOWN:", str(exc))
