"""A closed height-two BMS fan inside the FIRST compressed p_init cap.

The whole symbolic diagram stays small.  This checks the finite transport
identities, not a BMS-length computation or a height-seven theorem.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
from check_entry import build_for_types


def low_start():
    d, p, o = build_for_types()
    d.deadline = time.monotonic() + 20
    d.max_points, d.max_owners, d.max_facts = 1400, 500, 25000
    T, G, j = o['Jnew'], o['G'], o['j']
    H = d.application(T, j)
    d.approximation(G, (j,), p['k2'])
    d.lift_approximations(T, ((G, (j,), p['k2']),), limit=1)
    d.image(H, p['k1'])
    d.image(T, p['k2'])
    d.saturate()
    same = lambda a, b: d.find(a) == d.find(b)
    assert same(d.image(H, p['k1']), o['chi'])
    theta = [p['k0'], p['k1'], p['mu'], o['chi']]
    for i in range(2, 6):
        theta.append(d.image(H, theta[i]))
    d.saturate()
    assert all(d.lt(a, b) for a, b in zip(theta, theta[1:]))
    assert same(theta[4], d.image(T, p['k2']))
    assert same(theta[6], d.image(T, p['k3']))
    assert d.lt(theta[6], o['xi'])
    for i in range(6):
        assert same(d.image(H, theta[i]), theta[i + 2])
    for i in range(3):
        assert same(d.image(G, theta[i]), theta[i + 1])
    return d, p, o, theta, G, H


def add_two_fan(d, theta, G, H):
    actors = {'g': G, 'K': H}
    definitions = [('a','K','K'), ('b','K','g'), ('c','a','b'),
                   ('d','c','K'), ('e','d','g'), ('f','e','K'),
                   ('g0','f','K'), ('r','g0','f'), ('p','f','b'),
                   ('s','r','d'), ('J','p','f'), ('L','s','g0')]
    for name, left, right in definitions:
        actors[name] = d.application(actors[left], actors[right])
        for point in theta[:6]:
            d.image(actors[name], point)
        d.saturate()
    alpha = d.image(actors['e'], theta[4])
    beta = d.image(actors['f'], theta[2])
    zeta = d.image(actors['f'], theta[4])
    eta = d.image(actors['r'], theta[3])
    rho = d.image(actors['r'], theta[5])
    d.saturate()
    order = [theta[5], beta, alpha, zeta, eta, rho, theta[6]]
    assert all(d.lt(a, b) for a, b in zip(order, order[1:]))
    source = theta[:3]
    target = [theta[3], theta[5], alpha, zeta]
    owners = [actors['f'], actors['J']]
    same = lambda a,b: d.find(a) == d.find(b)
    for i, owner in enumerate(owners, 1):
        assert same(d.critical[owner], source[0])
        for x, y in zip(source[:i+1], target[:i+1]):
            assert same(d.image(owner, x), y)
        assert same(d.image(owner, target[0]), target[i+1])
    assert same(d.critical[actors['L']], target[0])
    assert same(d.image(actors['L'], target[0]), target[-1])
    assert same(d.image(actors['L'], target[-1]), rho)
    d.audit()
    return {'source': source, 'target': target, 'owners': owners,
            'connector': actors['L'], 'cap': rho}, actors


def main():
    started = time.monotonic()
    d, p, o, theta, G, H = low_start()
    fan, actors = add_two_fan(d, theta, G, H)
    assert d.lt(fan['cap'], theta[6]) and d.lt(theta[6], o['xi'])
    report = {'status': 'PASS', 'height': 2,
              'endpoint': 'rho < T(gamma4) < xi < eta < Sigma',
              'theta': ['kappa0', 'kappa1', 'mu', 'chi', 'T(kappa2)',
                        'H(chi)', 'T(kappa3)', 'H(H(chi))'],
              'fan': fan, 'actors': actors, 'diagram': d.summary(),
              'seconds': round(time.monotonic()-started, 3),
              'height_seven_proved': False,
              'scope': 'Finite closed-fan initialization. R2 has small descent count 22.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
