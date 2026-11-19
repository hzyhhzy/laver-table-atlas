"""Audit all 25 ordinary-BLP rows strictly below J13(gamma16).

Published scaling and quotient congruences are explicit proof inputs.
This checks actual finite point profiles, not an enormous BLP trajectory.
The transporter is the cheaper Jnew, NOT the former q(J10).
"""

import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
import bridge_probe as blp
from check_entry import build_for_types

INIT_ROWS = ((0, 1, 2), (0, 1, 2, 3), (0, 1, 2, 3, 4),
             (0, 1, 2, 3, 4, 5), (0, 1, 2, 3, 5, 6),
             (0, 1, 2, 3, 5, 6, 7), (0, 1, 2, 3, 5, 6, 7, 8))
INIT_STEPS = (1, 1, 2, 2, 3, 3, 3)


def verify(d, points, rows, steps, witnesses):
    pattern = blp.BLP(tuple(rows), tuple(steps))
    pattern.validate()
    assert len(points) == len(rows) + 2
    assert all(d.lt(x, y) for x, y in zip(points, points[1:]))
    edges = 0
    for row, step, owner in zip(rows, steps, witnesses):
        assert d.find(d.critical[owner]) == d.find(points[row[0]])
        for x, y in zip(row[:-step], row[step:]):
            assert d.find(d.image(owner, points[x])) == d.find(points[y])
            edges += 1
    return pattern, edges


def pinit(d, alpha, beta, a, b, c, mid, end, G, H):
    HH = d.application(H, H)
    HG = d.application(H, G)
    D = d.application(HH, HG)
    E = d.application(D, H)
    F = d.application(E, G)
    L = d.application(F, H)
    for actor in (HH, HG, D, E, F, L):
        for point in (alpha, beta, a, b, c, mid):
            d.image(actor, point)
    u, v = d.image(L, a), d.image(F, c)
    d.image(L, u)
    d.image(L, v)
    d.saturate()
    points = [alpha, beta, a, b, c, mid, u, v, end]
    actors = (G, G, H, H, L, L, L)
    verify(d, points, INIT_ROWS, INIT_STEPS, actors)
    return points, actors


def audit_marked_entry(rows, steps, owners):
    """Check the entry hypotheses of the existing finite marked-BLP bridge.

    This checks one initial certificate, not an unfolding experiment.
    Each chosen mark has a one-factor trace whose owner is globally equal
    to its carrier, so no speculative truncation equality is supplied.
    """
    cores = [row[:-1] for row in rows]
    marks = [set() for _ in rows]
    for block in range(4):
        rename = lambda x: x if x < 2 else x + 6 * block
        for row, source_marks in ((4, (3,)), (6, (5,)), (7, (5, 6))):
            marks[rename(row) - 1].update(rename(x) for x in source_marks)
    sat_receipts, mark_receipts = [], []
    for row_no, (core, step, row_marks) in enumerate(zip(cores, steps, marks), 1):
        assert core[-1] == row_no
        root, end = core[-step - 1], core[-step]
        if len(core) <= 2 * step:
            assert end >= 1
            previous = cores[end - 1][-2]
            assert previous <= root
            sat_receipts.append({'row': row_no, 'p': root, 'e': end,
                                 'B(e)': previous})
        for y in sorted(row_marks):
            pos = core.index(y)
            assert pos >= step and y < row_no
            delta = core[pos - step]
            assert delta >= 1
            trace_next = cores[y - 1][-steps[y - 1] - 1]
            assert trace_next == delta
            assert owners[row_no - 1] == owners[y - 1]
            mark_receipts.append({'row': row_no, 'mark': y,
                                  'trace': [y, delta], 'PosSource': True,
                                  'semantics': 'carrier = factor globally'})
    assert len(mark_receipts) == 16
    assert len(sat_receipts) == 13
    return {'status': 'PASS for all initial hypotheses',
            'Sat': sat_receipts, 'marks': mark_receipts,
            'quantitative_bridge': 'marked-BLP-quantitative-transfer.zh-CN.md',
            'scope': 'Initial marked certificate only; recursive closure is the cited paper theorem'}


def main():
    started = time.monotonic()
    d, p, o = build_for_types()
    d.deadline = time.monotonic() + 30
    d.max_points, d.max_owners, d.max_facts = 2500, 600, 50000
    T, G, j = o['Jnew'], o['G'], o['j']
    H = d.application(T, j)
    for point in (p['k0'], p['k1'], p['k2'], p['mu']):
        d.image(H, point)
    d.saturate()
    # g=q(j)==_k2 j; lift by T. The actual H-side output is guarded.
    d.approximation(G, (j,), p['k2'])
    d.lift_approximations(T, ((G, (j,), p['k2']),), limit=1)
    d.saturate()
    same = lambda x, y: d.find(x) == d.find(y)
    assert d.lt(d.image(H, p['k1']), d.image(T, p['k2']))
    assert same(d.image(H, p['k1']), o['chi'])
    assert same(d.image(T, p['mu']), o['xi'])
    assert d.lt(o['xi'], p['Sigma'])

    gamma = {0: p['k0'], 1: p['k1'], 2: p['k2'], 3: p['gamma3'],
             4: p['k3'], 16: p['gamma16'], 256: p['mu']}
    for n in (5, 8, 17, 32, 64, 65, 128):
        gamma[n] = d.point('gamma' + str(n))
    d.chain([gamma[n] for n in sorted(gamma)])
    D4 = o['actual_entry']['E']  # actual J14
    D16 = d.base(gamma[1])  # published actual J65534, kept compressed
    for actor, scale, arguments in ((D4, 4, (1, 2, 4)),
                                    (D16, 16, (1, 2, 4, 8, 16))):
        for n in arguments:
            d.record(actor, gamma[n], gamma[scale * n])
    R = [j, d.application(D4, j), d.application(D16, j)]
    R.append(d.application(D16, R[1]))
    for i, actor in enumerate(R):
        s = 4 ** i
        d.record(actor, gamma[1], gamma[s + 1])
        for n in (0, s, 2 * s):
            d.image(actor, gamma[n])
        if i:
            d.approximation(actor, (R[i - 1],) * 3, gamma[s + 1])
    d.saturate()
    for i, actor in enumerate(R):
        s = 4 ** i
        for n, m in ((0, s), (s, 2 * s), (2 * s, 4 * s)):
            assert same(d.image(actor, gamma[n]), gamma[m])

    high = [d.application(T, actor) for actor in R]
    stage_points = []
    for i, actor in enumerate(high):
        a, b = d.image(actor, p['k0']), d.image(actor, p['k1'])
        c, mid = d.image(actor, a), d.image(actor, b)
        end = d.image(actor, c)
        d.image(actor, p['mu'])
        stage_points.append((a, b, c, mid, end))
        if i:
            d.lift_approximations(
                T, ((R[i], (R[i - 1],) * 3, gamma[4 ** i + 1]),), limit=1)
    d.saturate()
    low = [G]
    for i in range(3):
        C = d.application(high[i], high[i])
        low.append(d.application(C, d.application(C, low[i])))
        for point in (p['k0'], p['k1'], stage_points[i + 1][0]):
            d.image(low[-1], point)
    d.saturate()

    global_points, global_rows, global_steps, global_owners = [], [], [], []
    receipts = []
    for i in range(4):
        a, b, c, mid, end = stage_points[i]
        s = 4 ** i
        assert same(a, d.image(T, gamma[s]))
        assert same(end, d.image(T, gamma[4 * s]))
        assert d.lt(b, d.image(T, gamma[s + 1]))
        points, owners = pinit(d, p['k0'], p['k1'], a, b, c, mid, end,
                               low[i], high[i])
        if not i:
            global_points.extend(points)
            first = 0
        else:
            assert same(global_points[-1], points[2])
            global_points.extend(points[3:])
            first = 1
        rename = lambda n: n if n < 2 else n + 6 * i
        global_rows.extend(tuple(rename(n) for n in row) for row in INIT_ROWS[first:])
        global_steps.extend(INIT_STEPS[first:])
        global_owners.extend(owners[first:])
        pattern, edges = verify(d, global_points, global_rows, global_steps, global_owners)
        assert len(pattern.rows) == 7 + 6 * i
        assert d.lt(end, p['Sigma'])
        receipts.append({'blocks': i + 1, 'rows': len(pattern.rows),
                         'endpoint': f'T(gamma_{4 * s})',
                         'all_rows_and_edges': 'PASS', 'edge_count': edges,
                         'strictly_below_Sigma': True})
    assert same(global_points[-1], o['xi'])
    assert same(d.image(o['B'], p['mu']), p['Sigma'])
    assert d.lt(p['k2'], p['mu']) and d.lt(o['xi'], p['Sigma'])
    marked_entry = audit_marked_entry(global_rows, global_steps, global_owners)
    d.audit()
    report = {
        'status': 'PASS',
        'transport': 'T=B0(j)(q(J2)), B0=q(J7), q=J13(J14)(J12)',
        'base_linedness': 8,
        'all_25_rows': True,
        'strict_endpoint': 'T(gamma256)=xi=B0(kappa2)<B0(mu)=Sigma',
        'Sigma': 'J13(gamma16)',
        'stages': receipts,
        'rows': global_rows, 'steps': global_steps,
        'numerical_bounds': ['N>2^f(P25,8)', 'N>2^(Psi^4(8)); Psi(m)=f(p_init,m)'],
        'marked_entry': marked_entry,
        'paper_inputs': ['new entry proof', 'Dougherty II Theorem 7.2(c), Lemma 7.1',
                         'published finite-quotient projection lemma',
                         'ordinary BLP quantitative theorem'],
        'scope': 'Every finite edge checked; published scaling and quantitative theorems are inputs, not Lean-certified here',
        'diagram': d.summary(), 'seconds': round(time.monotonic() - started, 3),
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('rows', 'steps', 'marked_entry')}, indent=2))
    print(json.dumps({'marked_entry': marked_entry['status'],
                      'checked_marks': len(marked_entry['marks']),
                      'checked_Sat_rows': len(marked_entry['Sat'])}))


if __name__ == '__main__':
    main()
