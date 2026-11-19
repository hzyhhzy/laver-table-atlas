"""Finite, incomplete equality and strict-order certificates for embeddings.

Different names do NOT assert different ordinals. Unknown images can be
named and later identified. An order is used only if justified by a stored
strict inequality, monotonicity, fixedness, or an application identity.
All points denote critical points in one Iter(j), not arbitrary ordinals.
"""

from __future__ import annotations

import time


class DiagramLimit(RuntimeError):
    pass


class PartialDiagram:
    def __init__(self, seconds=20, max_points=1800, max_owners=3500,
                 max_facts=120_000):
        self.started = time.monotonic()
        self.deadline = self.started + seconds
        self.max_points, self.max_owners = max_points, max_owners
        self.max_facts = max_facts
        self.parent, self.reach, self.labels = [], [], []
        self.critical, self.maps = [], []
        self.derived, self.apps = {}, {}
        self.alternatives, self.equal_owners = {}, set()
        self.ld_expanded = set()
        self.approximations, self.approx_keys = [], set()
        self.gap_instances = set()
        self.revision = self.merges = self.identities = 0

    def check(self):
        if time.monotonic() >= self.deadline:
            raise DiagramLimit("time limit")
        if len(self.parent) >= self.max_points:
            raise DiagramLimit("point-name limit")
        if len(self.maps) >= self.max_owners:
            raise DiagramLimit("owner limit")
        if sum(map(len, self.maps)) >= self.max_facts:
            raise DiagramLimit("fact limit")

    def point(self, label):
        self.check()
        p = len(self.parent)
        self.parent.append(p)
        self.reach.append(0)
        self.labels.append(label)
        return p

    def find(self, p):
        while self.parent[p] != p:
            self.parent[p] = self.parent[self.parent[p]]
            p = self.parent[p]
        return p

    def lt(self, a, b):
        a, b = self.find(a), self.find(b)
        return bool(self.reach[a] & (1 << b))

    def le(self, a, b):
        return self.find(a) == self.find(b) or self.lt(a, b)

    def edge(self, a, b):
        a, b = self.find(a), self.find(b)
        assert a != b and not self.lt(b, a), ("strict-order conflict", a, b)
        if self.lt(a, b):
            return
        mask = (1 << b) | self.reach[b]
        for x in range(len(self.parent)):
            if self.parent[x] == x and (x == a or self.reach[x] & (1 << a)):
                self.reach[x] |= mask
                assert not self.reach[x] & (1 << x)
        self.revision += 1

    def chain(self, points):
        for a, b in zip(points, points[1:]):
            self.edge(a, b)

    def merge(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return a
        assert not self.lt(a, b) and not self.lt(b, a), (
            "equality contradicts a proved order", a, b,
            self.labels[a], self.labels[b])
        a, b = min(a, b), max(a, b)
        self.parent[b] = a
        old_b, bit_a = 1 << b, 1 << a
        self.reach[a] |= self.reach[b]
        for x in range(len(self.parent)):
            if self.parent[x] == x and self.reach[x] & old_b:
                self.reach[x] = (self.reach[x] & ~old_b) | bit_a
        self.reach[a] &= ~old_b
        self.reach[b] = 0
        for x in range(len(self.parent)):
            if self.parent[x] == x and (x == a or self.reach[x] & bit_a):
                self.reach[x] |= self.reach[a]
                assert not self.reach[x] & (1 << x)
        self.revision += 1
        self.merges += 1
        return a

    def pairs(self, owner):
        result = {}
        for x, y in tuple(self.maps[owner].items()):
            x, y = self.find(x), self.find(y)
            if x in result:
                y = self.merge(result[x], y)
            result[x] = y
        self.maps[owner] = result
        return tuple((self.find(x), self.find(y)) for x, y in result.items())

    def record(self, owner, x, y):
        x, y = self.find(x), self.find(y)
        for u, v in self.pairs(owner):
            if self.find(u) == x:
                y = self.merge(y, v)
            if self.find(v) == self.find(y):
                x = self.merge(x, u)  # Injectivity.
        x, y = self.find(x), self.find(y)
        if self.maps[owner].get(x) != y:
            self.maps[owner][x] = y
            self.revision += 1
        self.order_facts(owner)
        return self.find(y)

    def order_facts(self, owner):
        pairs = self.pairs(owner)
        critical = self.find(self.critical[owner])
        for x, y in pairs:
            x, y = self.find(x), self.find(y)
            if self.lt(x, critical):
                self.merge(x, y)
            elif self.le(critical, x):
                # No Iter(j) critical point >= crit(owner) is fixed:
                # a fixed such point would bound its infinite critical
                # sequence in the locally finite critical-point set.
                self.edge(x, y)
        for at, (x, y) in enumerate(pairs):
            for u, v in pairs[:at]:
                if self.lt(x, u):
                    self.edge(y, v)
                elif self.lt(u, x):
                    self.edge(v, y)
                if self.lt(y, v):
                    self.edge(x, u)
                elif self.lt(v, y):
                    self.edge(u, x)

    def known(self, owner, source, depth=0):
        source = self.find(source)
        direct = None
        for x, y in self.pairs(owner):
            if self.find(x) == source:
                direct = self.find(y)
                break
        if self.lt(source, self.critical[owner]):
            if direct is not None:
                self.merge(direct, source)
            return self.find(source)
        if direct is not None or depth >= 24:
            return direct
        for actor, inner in self.decompositions(owner):
            before = self.preimage(actor, source)
            if before is not None:
                middle = self.known(inner, before, depth + 1)
                if middle is not None:
                    return self.known(actor, middle, depth + 1)
        return None

    def preimage(self, owner, point):
        point = self.find(point)
        if self.lt(point, self.critical[owner]):
            return point
        for x, y in self.pairs(owner):
            if self.find(y) == point:
                return self.find(x)
        return None

    def image(self, owner, source, depth=0):
        self.check()
        source = self.find(source)
        known = self.known(owner, source)
        if known is not None:
            return self.record(owner, source, known)
        for actor, inner in self.decompositions(owner) if depth < 40 else ():
            before = self.preimage(actor, source)
            if before is not None:
                middle = self.image(inner, before, depth + 1)
                value = self.image(actor, middle, depth + 1)
                self.identities += 1
                return self.record(owner, source, value)
        value = self.point(f"e{owner}(p{source})")
        return self.record(owner, source, value)

    def decompositions(self, owner):
        first = (self.derived[owner],) if owner in self.derived else ()
        return first + tuple(self.alternatives.get(owner, ()))

    def identify_owners(self, first, second):
        """Store a justified global owner identity, never a signature match."""
        pair = tuple(sorted((first, second)))
        if first != second and pair not in self.equal_owners:
            self.equal_owners.add(pair)
            self.revision += 1

    def expand_ld(self, owners, limit=60):
        """Add a(b(c)) = a(b)(a(c)); no finite-signature identifications."""
        count = 0
        for owner in owners:
            for actor, inner in self.decompositions(owner):
                if inner not in self.derived:
                    continue
                key = owner, actor, inner
                if key in self.ld_expanded:
                    continue
                self.check()
                self.ld_expanded.add(key)
                left, right = self.derived[inner]
                a = self.application(actor, left)
                b = self.application(actor, right)
                if (a, b) in self.apps and self.apps[a, b] != owner:
                    other = self.apps[a, b]
                    self.identify_owners(owner, other)
                else:
                    self.apps[a, b] = owner
                pair = a, b
                if pair not in self.decompositions(owner):
                    self.alternatives.setdefault(owner, []).append(pair)
                count += 1
                if count >= limit:
                    return count
        return count

    def base(self, critical):
        self.check()
        owner = len(self.maps)
        self.critical.append(self.find(critical))
        self.maps.append({})
        return owner

    def application(self, actor, inner):
        key = actor, inner
        if key not in self.apps:
            critical = self.image(actor, self.critical[inner])
            result = self.base(critical)
            self.derived[result] = key
            self.apps[key] = result
            self.approximation(result, (inner,), self.critical[actor])
        result = self.apps[key]
        for x, y in self.pairs(inner):
            ax, ay = self.known(actor, x), self.known(actor, y)
            if ax is not None and ay is not None:
                self.record(result, ax, ay)
        return result

    def approximation(self, owner, word, cutoff):
        """Membership-truncated equality, with word read outermost first."""
        key = owner, tuple(word), self.find(cutoff)
        if key not in self.approx_keys:
            self.approx_keys.add(key)
            self.approximations.append(key)

    def lift_approximations(self, actor, records=None, limit=40):
        records = tuple(self.approximations if records is None else records)
        count = 0
        for owner, word, cutoff in records:
            self.check()
            moved = self.application(actor, owner)
            factors = tuple(self.application(actor, e) for e in word)
            self.approximation(moved, factors, self.image(actor, cutoff))
            count += 1
            if count >= limit:
                break
        return count

    def congruence_at(self, cutoff, owners=None, limit=100, single_only=False):
        """Apply existing left-factor approximations at ONE fixed cutoff.

        If a agrees with b_0 circ ... circ b_k below cutoff, then
        a(c) agrees there with b_0(b_1(...(b_k(c))...)).  This is
        membership congruence, not left pointwise monotonicity.
        The owner list is snapshotted; the caller bounds further rounds.
        """
        owners = tuple(self.derived if owners is None else owners)
        added = 0
        for owner in owners:
            for actor, inner in self.decompositions(owner):
                candidates = tuple((word, bound) for a, word, bound
                    in self.approximations if a == actor
                    and self.find(bound) == self.find(cutoff)
                    and word != (actor,) and (not single_only or len(word) == 1))
                if single_only and candidates:
                    candidates = (min(candidates),)
                for word, bound in candidates:
                    self.check()
                    alternative = inner
                    for factor in reversed(word):
                        alternative = self.application(factor, alternative)
                    if alternative == owner:
                        continue
                    key = owner, (alternative,), self.find(bound)
                    if key not in self.approx_keys:
                        self.approximation(owner, (alternative,), bound)
                        added += 1
                        if added >= limit:
                            return added
        return added

    def read_approximations(self):
        # Only previously named input/output facts are queried.  A value at
        # or above the cutoff is never read as an equality.
        for owner, word, cutoff in tuple(self.approximations):
            self.check()
            for x, y in self.pairs(owner):
                if not self.lt(y, cutoff):
                    continue
                value = x
                for factor in reversed(word):
                    value = self.image(factor, value)
                try:
                    self.merge(y, value)
                except AssertionError as exc:
                    raise AssertionError({"rule": "read below membership cutoff",
                        "owner": owner, "word": word, "cutoff": cutoff,
                        "input": x, "owner_value": y, "word_value": value,
                        "cause": exc.args}) from exc
            candidates = self.pairs(word[-1])
            for x, first in candidates:
                value = first
                for factor in reversed(word[:-1]):
                    value = self.known(factor, value)
                    if value is None:
                        break
                if value is not None and self.lt(value, cutoff):
                    self.record(owner, x, value)

    def gap_bound(self, actor, base_j, kappa1, gamma3, point):
        """Dougherty I, section 5 (dagger), with its strict input guard."""
        first = self.image(actor, kappa1)
        if not self.lt(point, first):
            return False
        key = actor, self.find(point)
        if key in self.gap_instances:
            return False
        image_j = self.application(actor, base_j)
        upper = self.image(actor, gamma3)
        once = self.image(image_j, point)
        twice = self.image(image_j, once)
        self.edge(twice, upper)
        self.gap_instances.add(key)
        return True

    def saturate(self, rounds=12):
        for turn in range(rounds):
            self.check()
            old = self.revision
            for owner in range(len(self.maps)):
                self.order_facts(owner)
            for a, b in tuple(self.equal_owners):
                self.merge(self.critical[a], self.critical[b])
                for x, y in self.pairs(a):
                    self.record(b, x, y)
                for x, y in self.pairs(b):
                    self.record(a, x, y)
                # True owner identity is a congruence in BOTH slots of
                # application.  Do not confuse this with equal finite maps.
                for (actor, inner), result in tuple(self.apps.items()):
                    alternate = (self.apps.get((b, inner)) if actor == a else
                                 self.apps.get((a, inner)) if actor == b else None)
                    if alternate is not None and alternate != result:
                        self.identify_owners(result, alternate)
                    alternate = (self.apps.get((actor, b)) if inner == a else
                                 self.apps.get((actor, a)) if inner == b else None)
                    if alternate is not None and alternate != result:
                        self.identify_owners(result, alternate)
            for owner in tuple(self.derived):
                for actor, inner in self.decompositions(owner):
                    self.merge(self.critical[owner],
                               self.image(actor, self.critical[inner]))
                    # Read a(b)(a(x)) = a(b(x)) in either direction when
                    # the required preimages are already known.  This
                    # does not assume that every point is in a's range.
                    for x, y in self.pairs(owner):
                        before = self.preimage(actor, x)
                        if before is None:
                            continue
                        middle = self.known(inner, before)
                        if middle is not None:
                            self.record(actor, middle, y)
                        else:
                            middle = self.preimage(actor, y)
                            if middle is not None:
                                self.record(inner, before, middle)
                    for x, y in self.pairs(inner):
                        ax, ay = self.known(actor, x), self.known(actor, y)
                        if ax is not None and ay is not None:
                            self.record(owner, ax, ay)
            self.read_approximations()
            if old == self.revision:
                return turn + 1
        return rounds

    def audit(self):
        self.check()
        for x in range(len(self.parent)):
            root = self.find(x)
            assert not self.reach[root] & (1 << root)
        for owner in range(len(self.maps)):
            self.order_facts(owner)

    def summary(self):
        roots = [x for x in range(len(self.parent)) if self.find(x) == x]
        return {"point_names": len(self.parent), "point_classes": len(roots),
                "proved_strict_pairs": sum(self.reach[x].bit_count() for x in roots),
                "owners": len(self.maps), "facts": sum(map(len, self.maps)),
                "merged_names": self.merges,
                "lazy_application_rewrites": self.identities,
                "ld_decompositions": len(self.ld_expanded),
                "owner_identity_pairs": len(self.equal_owners),
                "membership_approximations": len(self.approximations),
                "proved_gap_instances": len(self.gap_instances)}
