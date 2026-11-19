"""Audit the new actual entry Qstar, without changing any old research file.

The source congruence A ==_mu j(J2) is a published paper input.
P ==_gamma16 E is obtained by transporting B ==_k2 j by B.
The program checks the cutoffs and every subsequent ordinal observation.
It never replaces K(gamma4)=oldTheta by the smaller new endpoint.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
from partial_embedding_diagram import PartialDiagram


def actual_entry():
    d = PartialDiagram(seconds=12, max_points=800, max_owners=180,
                       max_facts=12000)
    names = ('k0', 'k1', 'k2', 'gamma3', 'k3', 'gamma16',
             'mu', 'chi', 'Sigma', 'oldTheta')
    p = {name: d.point(name) for name in names}
    d.chain(list(p.values()))
    j = d.base(p['k0'])
    for src, dst in (('k0', 'k1'), ('k1', 'k2'), ('k2', 'k3')):
        d.record(j, p[src], p[dst])
    powers = {1: j}
    for a in range(2, 15):
        powers[a] = d.application(powers[a - 1], j)
    K, A, B, E = (powers[a] for a in (11, 12, 13, 14))
    small_profiles = {
        3: (('k1', 'gamma3'),),
        7: (('k0', 'gamma3'), ('k1', 'k3'), ('k2', 'mu')),
        11: (('k0', 'k2'), ('k1', 'k3'), ('k2', 'mu'),
             ('gamma3', 'chi'), ('k3', 'oldTheta')),
        12: (('k2', 'k3'), ('k3', 'mu'), ('mu', 'oldTheta')),
        13: (('k0', 'k1'), ('k1', 'k3'), ('k2', 'gamma16'),
             ('k3', 'mu'), ('gamma16', 'Sigma')),
        14: (('k1', 'k3'), ('k3', 'gamma16')),
    }
    for a, profile in small_profiles.items():
        for src, dst in profile:
            d.record(powers[a], p[src], p[dst])
    U = d.application(A, A)
    P = d.application(B, B)
    P2 = d.application(P, P)
    X = d.application(B, E)
    PE = d.application(P, E)
    d.identify_owners(PE, X)  # B(B)(B(j))=B(B(j)).
    Qold = d.application(K, powers[3])
    d.identify_owners(Qold, d.application(U, A))
    Y = d.application(X, A)
    for o in (U, P, P2, X, Qold, Y):
        for name in ('k0', 'k1', 'k2', 'k3', 'gamma16', 'mu'):
            d.image(o, p[name])
    d.saturate()
    same = lambda u, v: d.find(u) == d.find(v)
    assert same(d.image(P, p['gamma16']), p['Sigma'])
    assert same(d.critical[X], p['k3'])
    assert same(d.image(X, p['k3']), p['mu'])
    assert same(d.image(X, p['mu']), p['Sigma'])
    assert same(d.critical[Y], p['k2'])
    assert same(d.image(Y, p['k2']), p['mu'])
    assert same(d.image(Y, p['mu']), p['Sigma'])
    assert same(d.image(Qold, p['k3']), p['chi'])
    assert same(d.image(Qold, p['mu']), p['oldTheta'])
    # PAPER: A ==_mu j(J2) gives U ==_oldTheta P(P) by LD.
    # B=A(j) ==_k2 j, since crit(A)=k2. Transport by B to get
    # P ==_gamma16 E, then by P, whose image of gamma16 is Sigma.
    # Finally first-argument congruence gives Y ==_Sigma Qold.
    assert d.lt(p['Sigma'], p['oldTheta'])
    assert d.lt(p['chi'], p['Sigma'])
    d.approximation(U, (P2,), p['oldTheta'])
    assert same(d.critical[A], p['k2'])
    d.approximation(B, (j,), p['k2'])
    d.lift_approximations(B, ((B, (j,), p['k2']),), limit=1)
    d.approximation(U, (X,), p['Sigma'])
    d.approximation(Y, (Qold,), p['Sigma'])
    d.saturate()
    assert same(d.image(Y, p['k3']), p['chi'])
    g = d.application(Y, j)
    gnext = d.application(Y, B)
    for o in (g, gnext):
        for name in ('k0', 'k1', 'mu', 'chi'):
            d.image(o, p[name])
    d.saturate()
    for src, dst in (('k0', 'k1'), ('k1', 'mu'), ('mu', 'chi')):
        assert same(d.image(g, p[src]), p[dst])
    for src, dst in (('k0', 'k1'), ('k1', 'chi'), ('chi', 'Sigma')):
        assert same(d.image(gnext, p[src]), p[dst])
    assert same(d.image(K, p['k3']), p['oldTheta'])
    assert d.lt(d.image(Y, p['mu']), d.image(Qold, p['mu']))
    d.audit()
    return d, p, dict(j=j, powers=powers, K=K, A=A, B=B, E=E,
                      U=U, P=P, X=X, Qold=Qold, Y=Y, g=g, gnext=gnext)


def build_for_types():
    """Build the universal type interface from the new concrete entry.

    No equality Y=K(j3) is assumed. K keeps its old, strictly larger cap.
    """
    d, p, entry = actual_entry()
    d.deadline = time.monotonic() + 15
    d.max_points, d.max_owners, d.max_facts = 1800, 450, 24000
    p['theta'] = p['Sigma']  # Only the generic interface's endpoint name.
    j = entry['j']
    j2, j3, j4, j7 = (entry['powers'][a] for a in (2, 3, 4, 7))
    Q = entry['Y']
    G = entry['g']
    G2, G3, G4, B = [d.application(Q, a) for a in (j2, j3, j4, j7)]
    d.identify_owners(G2, d.application(G, G))
    d.identify_owners(G3, d.application(G2, G))
    d.identify_owners(G4, d.application(G3, G))
    delta, chi = (d.image(Q, p[name]) for name in ('gamma3', 'k3'))
    xi = d.image(B, p['k2'])
    E = d.application(B, j)
    Jnew = d.application(E, G2)
    Knew = d.application(Jnew, G)
    EG, EG3 = d.application(E, G), d.application(E, G3)
    d.identify_owners(EG3, d.application(Jnew, EG))
    for actor in (G2, G3, G4, B, E, Jnew, Knew, EG, EG3):
        for point in (p['k0'], p['k1'], p['k2'], p['mu'], delta, chi):
            d.image(actor, point)
    d.saturate()
    same = lambda a, b: d.find(a) == d.find(b)
    for actor, src, dst in ((B, 'mu', 'theta'),
                             (Jnew, 'k1', 'mu')):
        assert same(d.image(actor, p[src]), p[dst])
    assert same(d.image(Jnew, p['mu']), xi)
    assert d.lt(p['mu'], delta) and d.lt(delta, chi)
    assert d.lt(chi, xi) and d.lt(xi, p['theta'])
    d.approximation(EG, (G,), delta)
    d.lift_approximations(Jnew, ((EG, (G,), delta),), limit=1)
    read_cut = d.image(Jnew, delta)
    assert same(d.image(EG3, p['k1']), chi)
    assert d.lt(chi, xi) and d.lt(xi, read_cut)
    d.saturate()
    assert same(d.image(Knew, p['k1']), chi)
    d.approximation(EG3, (G3,), delta)
    d.approximation(Knew, (G3,), delta)
    d.audit()
    o = dict(j=j, j2=j2, j3=j3, K=entry['K'], Q=Q, G=G, G2=G2,
             G3=G3, G4=G4, B=B, A=E, Jnew=Jnew, Knew=Knew,
             delta=delta, chi=chi, xi=xi, actual_entry=entry)
    return d, p, o


if __name__ == '__main__':
    d, p, _ = actual_entry()
    # Integers used in the elementary four-point lower bound, not the
    # enormous final power of two.
    length = 2048
    next_length = length * (1 << length)
    assert next_length == 1 << 2059
    report = {
        'status': 'PASS',
        'new_entry': 'Y=J13(J14)(J12), application left-associated',
        'profile': 'crit gamma2; gamma2->gamma256; gamma4->chi; gamma256->Sigma',
        'Sigma': 'J13(gamma16)',
        'paper_congruences': ['A==_mu j(J2); its A-image is U==_oldTheta P(P)'],
        'derived_congruence': 'B=A(j)==_k2 j; its B-image is P==_gamma16 J14',
        'read_guard': 'Qold(gamma4)=chi<Sigma',
        'endpoint_not_read_through_cut': 'Y(mu)=Sigma<oldTheta=Qold(mu)',
        'new_four_point_chain': 'Y(J13): gamma0->gamma1->chi->Sigma',
        'elementary_index_lower': '2^(2^2059)',
        'diagram': d.summary(),
        'seconds': round(time.monotonic() - d.started, 3),
        'scope': 'Finite geometry and explicit proof-input audit, not Lean or exhaustive large-table evaluation',
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report))
