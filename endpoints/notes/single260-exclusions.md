# Expanding to the search for single-layer images up to 260: new excluded results and unresolved ranges · [中文版](single260-exclusions.zh-CN.md)

2026-11-09. The usual presentation of fixing I3 into $j$. This text is a paper derivation, not a new formalization of Lean, and does not claim to complete a pure ZFC finite table translation.

Let (J_1=j, J_{a+1}=J_a(j))) be the set of all points in the plane, where the brackets between the elements indicate application.

$$
\chi=J_{11}(\gamma_3),\qquad
\Sigma=J_{13}(\gamma_{16}),\qquad
\Theta=J_{11}(\gamma_4).
$$

The user is looking for a single-term expression $J_a(\gamma_b)$, with two parameters not exceeding 260, and satisfying $\chi<J_a(\gamma_b)<\Sigma$. Any known multi-factor application terms, even if short, are not considered solutions to this problem.

The new step of **Current actual conclusion: For all $1\le a\le16$ and all natural numbers (b)), such a formula does not exist.** is to rule out the possibility that (J_{12},J_{14})) remain between $\gamma_{16}$ and $\gamma_{256}$. The search for $17\le a\le260$ is not yet complete; no evidence has been found that does not prove their non-existence.

## 1. depends on and notation

Basic sources:

- [Dougherty I, Section 5](https://arxiv.org/pdf/math/9205202).
- [Dougherty II, Lemma 6.2, Section 8, and Cut-off Rules](https://arxiv.org/pdf/math/9503204).
- [Previous gap proof](j13-gamma13-15-below-chi.md).
- [A complete lower-end spectrum proof for Q](c5-linear-prefix-and-q-spectrum.md).

The following text indeed relies on the paper theorem mentioned at the end. It does not consider the calculation of several examples as proof of the theorem.

Put

$$
K=J_{11},\ A=J_{12},\ B=J_{13},\ E=J_{14},\ F=J_{15},
\quad \mu=\gamma_{256},
$$

$$
\sigma=j(<\kappa_1),\quad\sigma_2=j(<\kappa_2),\quad
\tau=j(\sigma),\quad S_i=J_i(\sigma),\quad T=A(\sigma_2).
$$

Among them, $f(<\alpha)=\sup_{\beta<\alpha}f(\beta)$,
$\kappa_0=\gamma_0,\kappa_1=\gamma_1,\kappa_2=\gamma_2,
\kappa_3=\gamma_4. Some conclusions are

$$
\gamma_3<S_3<S_2<\tau<\sigma_2<\kappa_3,
\quad T=B(<\kappa_3)<S_{11}=A(<\kappa_3)<\mu.
\tag{1}
$$

Let $s=B(\sigma)$. The previous gap proof is given as follows

$$
s=A(\tau)=j(S_2),\qquad
\gamma_{15}<s<\gamma_{16},
\tag{2}
$$

$$
B(<s)<A(\gamma_{16})<\chi<B(s),
\qquad A(<S_{11})<\chi.
\tag{3}
$$

Here, (s=j(S_2)) uses $B|V_{\kappa_2}=(j\circ J_2)|V_{\kappa_2}$ and $\sigma<\kappa_2$. These are uses of the ordinary limits, without directly substituting their endpoints.

## 2. places several non-critical boundaries between gamma255 and gamma256

First, we have $S_{14}=E(\sigma)=J_2(S_2)$. The reason is that it is known as such.

$$
E\equiv_{\gamma_8}J_2\circ J_2,\qquad E(\kappa_2)=\gamma_8.
$$

For the input $\sigma<\kappa_2$, one side outputs $E(\sigma)<\gamma_8$. Therefore, the strict output guard with member truncation allows this equality to be read.

Due to the consistency of (F=E(j)),

$$
F(S_{14})=E(j(\sigma))=E(\tau)>E(\gamma_3)=\gamma_{12}.
$$

Dougherty II Lemma 6.2 gives $F(\gamma_7)=\gamma_{11}$ (where the shift amount is 4, and the input 7 is strictly less than 8). Since (F) is strictly increasing,

$$
\gamma_7<S_{14}.
\tag{4}
$$

Let (Q=B(J_2)=E(E)), (v=B(S_2))). The cited spectrum theorem provides

$$
Q(\gamma_{255})=\gamma_{13107}.
\tag{5}
$$

Consistency, (4) and the proven $B(\gamma_7)=\gamma_{16384}$ are given

$$
Q(v)=B(J_2(S_2))=B(S_{14})
>B(\gamma_7)=\gamma_{16384}>Q(\gamma_{255}).
$$

So $\gamma_{255}<v$. Using (1), we get a strict chain.

$$
\boxed{\gamma_{255}<B(S_2)<B(\tau)<T<S_{11}<\gamma_{256}.}
\tag{6}
$$

The strictness of $B(\tau)<T=B(<\kappa_3)$ can be defined by a ordinal number between $\tau$ and $\kappa_3$, using monotonicity; it is not defined solely by the supremum, directly writing less than or equal to as strictly less than.

## The input that excludes all inputs of J12 is 3..

(6) and (3) provide)

$$
A(\gamma_{255})\le A(<S_{11})<\chi.
\tag{7}
$$

On the other hand, (A=K(j)), $K(\kappa_2)=\mu$ provide

$$
A(\gamma_{256})=A(K(\kappa_2))=K(j(\kappa_2))
=K(\kappa_3)=\Theta>\Sigma.
\tag{8}
$$

Due to strict increasingness, the integer inputs are all less than the left endpoint when $b\le255$, and all greater than the right endpoint when $b\ge256$. Therefore, there is no desired formula for this entire row.

## The input that excludes all inputs of J14 is 4..

This section additionally checks the strictness of suprems. It cannot be directly inferred from the strict increase of $j$.
(j(<S_2)<j(S_2)).

Because $\operatorname{cf}(\sigma)=\kappa_1$, the primacy is given

$$
\operatorname{cf}(S_2)=J_2(\kappa_1)=\kappa_2.
$$

$\kappa_2$ is regular and $j(\kappa_2)=\kappa_3>\kappa_2$. Take a common tail sequence of length $\kappa_2$ and apply $j$ to it, such that the first $j``\kappa_2$ part is bounded in the image sequence of length $j(\kappa_2)$, thereby

$$
j(<S_2)<j(S_2)=s.
\tag{9}
$$

The supremum transport formula and (E=B(j)) provide

$$
E(<v)=B(j(<S_2))\le B(<s)<\chi.
\tag{10}
$$

Given (6),

$$
E(\gamma_{255})\le E(<v)<\chi.
\tag{11}
$$

At the next integer input, use $B(\kappa_3)=\mu$:

$$
E(\gamma_{256})=E(B(\kappa_3))=B(j(\kappa_3))
=B(\kappa_4)>\kappa_4>\Theta>\Sigma.
\tag{12}
$$

Therefore, the entire line of (J_{14})) is also excluded.

## Exclude all lines where 5. appears and a<=16 appears.

[Previous 272 item classification](no-single-j-gamma16-between-chi-Sigma.md) has already processed $b\le16$. For the following rows, it is known that the smallest input that strictly exceeds $\Theta$ does not exceed 16:

| a | A proven input that exceeds Theta: b |
| --- | --- |
| 1,2,3,4 | 4 |
| 5,6 | 2 |
| 7 | 3 |
| 8 | 6 |
| 9,10 | 3 |
| 11 | 5 |
| 15 | 16 |
| 16 | 8 |

Therefore, all the remaining inputs in these lines exceed $\Sigma$. The 13 line equals $b=16$ exactly at $\Sigma$, and strictly exceeds it thereafter. The 12 and 14 lines are dealt with in the third and fourth sections. This proves the universal exclusion stated at the beginning of this document.

## 6. expands the precise range of the search.

`search_single260.py` establishes a finite partial order using co-commutativity, strict monotonicity, explicit lower-end equality, and application blocks with truncation guards. It is not a definitive procedure for the entire rectangle, as points that the procedure fails to compare remain unresolved. The product in the finite set of natural numbers being zero only indicates saturation at that order, but does not prove that it exceeds $\chi$ or $\Sigma$.

The witness in $1\le a\le260, 0\le b\le260$ has not yet been obtained. A smaller unresolved point is

$$
J_{24}(\gamma_4)=J_{25}(\gamma_2)=J_{26}(\gamma_2)
=J_{27}(\gamma_2)=J_{28}(\gamma_5).
$$

These equal signs are due to the consistency of successive application and
$J_{24}(\gamma_2)=\gamma_2, J_{25}(\gamma_1)=\gamma_2,
J_{26}(\gamma_1)=\gamma_2, J_{27}(\gamma_1)=\gamma_5$
Read it. It's just a different way of writing the same unresolved point; there is no proof that it falls within the target interval.

`probe_suprema260.py/.json` records the finite relation reviews for sections two to four. The script refers to the paper-based derivations of (4), (9)—(10) as explicit premises; therefore, the script does not provide independent formal proofs that do not constitute a deduction from these supremum premises.
