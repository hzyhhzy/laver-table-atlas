# Tail-locality for the typed hierarchy comparisons · [中文版](hardy-root-tail-locality.zh-CN.md)

*The working paper was written in English. Its title links to the Chinese translation.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-15. This fills an explicit admissibility condition: arbitrary
monotone extensive higher operators need NOT ignore an input's value
at 1 when they are evaluated at 2. Our constructed recursors do.

At type zero let X0 consist of nondecreasing extensive functions on
positive integers. For every b>=1 define f<=_b g iff f(x)<=g(x) for
all x>=b. At type one restrict to operators which preserve EVERY
tail preorder <=_b, in addition to the previously required monotonicity
and extensiveness. For admitted T,U define T<=_b U iff
  for every admitted f, T(f)<=_b U(f).
Then f<=_b g and T<=_b U imply T(f)<=_b U(g). This is the mixed form
used in induction. Tail equivalence implies output tail equivalence,
so these operators are genuinely tail-local, not just usually monotone.

Inductively at higher types use the same hereditary construction:
operators must preserve each lower-type tail preorder, and comparison
is pointwise on every admitted lower-type argument. The mixed form
follows at every type. All assertions below concern this restricted
class, not arbitrary set-theoretic functions between the type domains.

Lemma. The original first-root source hierarchy, ordinary BMS relative
hierarchy, fast BMS hierarchy, and their final-input diagonal operators
preserve each tail preorder in every base/argument. In particular their
values at final x>=b depend only on each relevant lower-type argument
on the same tail.

Proof. Simultaneous well-founded induction on the source/BMS index.
The empty case invokes the admitted base. At scalar successors, all
intermediate numeric inputs are >=the starting x, by extensiveness;
the lower-index tail comparison therefore applies at every iterate.
At a higher-type successor first fix the final x>=b. Finite induction
on n gives T^n(f)<=_b U^n(g) from T<=_b U and f<=_b g. Set n=x,
x+1, or 2^x as prescribed, then evaluate at x. Since the argument holds
for EVERY x>=b, the resulting final-input diagonal itself preserves the
tail relation. Higher arguments are handled by the same mixed relation.
At a non-successor, after fixing final x the selected child is the
same on both sides; apply the smaller-index simultaneous induction.
If comparing two notations through a cover, the already proved finite
cover path is used at that fixed x, and the successor induction was
universally quantified over bases and all inputs on the tail. Thus no
x-specific whole-object inequality is smuggled into an iteration.

The scalar Btilde diagonal uses a seed height h(x) depending on final x.
This causes no issue: for each fixed x>=b both compared values use
the SAME h(x), and the fixed-index tail comparison applies. The usual
seed-height argument separately proves final-input monotonicity.
This proves the lemma.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

If a source object is initially defined only for x>=2, extend it
admissibly by Hhat_A(1)=2 and Phihat(f)(1)=f(1), preserving all exact
values for x>=2. Extensiveness ensures monotonicity across the boundary.
All relevant type relations and final source identities are on the
tail x>=2, so these choices do not assume that the special original
[1] behavior itself belongs to the chosen all-domain type class.

Independent original-target audit approved this lemma and recommended
the explicit extension sentence just added. The review is local to
this technical admissibility point, not a new proof of every old cover.

[Original manuscript](<hardy-root-tail-locality.txt>)
