"""Audit lower iteration caps; do not assume their order against Q(gamma16).

Only a small actual-embedding diagram is constructed. Source scaling,
the shift-word lemma, and BLP quantitative transfer are paper inputs.
"""
from pathlib import Path
import json
import sys
import time

sys.dont_write_bytecode = True
from check_low_two_fan import low_start
from check_blp25 import verify, INIT_ROWS, INIT_STEPS, pinit


def main():
    started = time.monotonic()
    d, p, o, theta, G, H = low_start()
    d.deadline = time.monotonic() + 20
    same = lambda a, b: d.find(a) == d.find(b)
    j, G2, e, T = o['j'], o['G2'], o['A'], o['Jnew']
    Qold = o['actual_entry']['Qold']
    U = d.image(Qold, p['gamma16'])
    # The old strict supremum theorem; no relation U versus theta[4:7]
    # is supplied as an input.
    d.edge(p['chi'], U)
    d.edge(U, o['xi'])

    gamma = {0: p['k0'], 1: p['k1'], 2: p['k2'], 4: p['k3'],
             256: p['mu'], 257: o['delta']}
    for n in (512, 513, 1024, 65536):
        gamma[n] = d.point('gamma' + str(n))
    d.chain([gamma[n] for n in sorted(gamma)] + [p['chi']])
    # Previously proved scaling G2(gamma_r)=gamma_(256r), r<256.
    d.record(G2, gamma[2], gamma[512])
    d.record(G2, gamma[4], gamma[1024])
    # A=G2(j) ==_gamma65536 J_(2^256-1); the latter shifts 257 to 513.
    A = d.application(G2, j)
    d.record(A, gamma[257], gamma[513])
    ej = d.application(e, j)
    T_ej = d.application(T, ej)
    e_A = d.application(e, A)
    d.identify_owners(T_ej, e_A)  # Left distributivity.
    d.approximation(ej, (j,), o['delta'])
    d.lift_approximations(T, ((ej, (j,), o['delta']),), limit=1)
    for actor in (H, T, e, e_A, T_ej):
        for point in (p['k1'], p['k2'], p['k3'], p['mu'],
                      o['delta'], gamma[512], gamma[513], gamma[1024], p['chi']):
            d.image(actor, point)
    d.saturate()
    assert d.lt(o['xi'], d.image(T, o['delta']))
    d.congruence_at(d.image(T, o['delta']), owners=(H, T_ej),
                    limit=6, single_only=True)
    d.saturate()

    caps = theta[4:7]
    for cap, n in zip(caps, (512, 513, 1024)):
        assert same(cap, d.image(e, gamma[n]))
    assert all(d.lt(a, b) for a, b in zip([p['chi']] + caps, caps + [o['xi']]))

    # Convert the smaller-entry e to the old short Q word by guarded reads.
    old_b = d.application(Qold, o['actual_entry']['powers'][7])
    old_e = d.application(old_b, j)
    d.approximation(old_e, (e,), p['Sigma'])
    for n in (512, 513, 1024):
        assert d.lt(d.image(e, gamma[n]), p['Sigma'])
        d.image(old_e, gamma[n])
    d.saturate()
    for n in (512, 513, 1024):
        assert same(d.image(old_e, gamma[n]), d.image(e, gamma[n]))

    # p1 has the first three rows. The next cap has p_start.del, NOT p2.
    first_rows = INIT_ROWS[:4]
    first_steps = INIT_STEPS[:4]
    receipts = []
    for count, name in ((3, 'p1'), (4, 'p_start.del')):
        pattern, edges = verify(d, theta[:count+2], first_rows[:count],
                                first_steps[:count], (G, G, H, H)[:count])
        receipts.append(dict(pattern=name, rows=count, edges=edges,
                             base_linedness=8, endpoint=f'e(gamma{(512,513)[count-3]})'))
    # One full seven-row p_init, with its inserted internal points.
    points, owners = pinit(d, *theta[:7], G, H)
    _, edges = verify(d, points, INIT_ROWS, INIT_STEPS, owners)
    receipts.append(dict(pattern='p_init', rows=7, edges=edges,
                         base_linedness=8, endpoint='e(gamma1024)'))
    d.saturate()
    comparison = []
    for cap, n in zip(caps, (512, 513, 1024)):
        result = ('U < cap' if d.lt(U, cap) else
                  'cap < U' if d.lt(cap, U) else
                  'U = cap' if same(U, cap) else 'UNRESOLVED')
        comparison.append(dict(cap=f'e(gamma{n})', relation=result))
    d.audit()
    record = dict(status='PASS',
        short_word='e=(Q(J7))(j), Q=J11(J3)',
        proved_order='chi < e(gamma512) < e(gamma513) < e(gamma1024) < xi',
        U_comparisons=comparison, structures=receipts,
        first_cap_lower_bound='index >= 2^(g^[256](8)) > 2^^259; g(m)=m*2^m',
        second_cap_lower_bound='index >= m_(omega+2)(2), by the published m=1 reduction',
        paper_inputs=['base 8-line', 'G2 scaling for r<256',
                      'delta=gamma257', 'G2(j) at gamma257 shifts to gamma513',
                      'ordinary BLP quantitative theorem',
                      'U<xi from the previous strict supremum proof'],
        scope='finite profiles and structural verification; no giant evaluation or inferred order',
        diagram=d.summary(), seconds=round(time.monotonic()-started, 3))
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
