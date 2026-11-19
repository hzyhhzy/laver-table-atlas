# Ordinary L=3 seeds: a primary native completion and positive source marking propagation · [中文版](ordinary-l3-native-mark-seed.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Fix the original $\operatorname{Iter}(j)$ under ZFC + I3. This paper presents all the actual owners of the eight-row seeds, proves that the first native completion is indeed non-empty, and demonstrates that this set is transmitted to the next row through a **Original Marking**. After a single scan, all rows still have actual owners, and the total end remains as $\theta_6<\kappa_4=j(\gamma_4)$.

This is not the full closure theorem, nor is it a lower bound stronger than BMS; it does not assume that this manual seed is reachable from the top of the original IBLP.

## 1. already has existing terms and only one new term added.

Following $K=j_{(11)}$, as well as $K(\theta_i)=\theta_{i+2}\;(0\le i\le5)$, $\theta_i=\kappa_i\;(0\le i\le3)$, $\theta_4=\mu$. The actual application items are

$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K),
$$

$$
g=f(K),\qquad H=g(f),\qquad
\alpha=e_*(\mu),\quad\beta=f(\kappa_2),\quad
\zeta=f(\mu),\quad\eta=H(\kappa_3).
\tag{1}
$$

All parentheses represent applications. For proofs with finite point images, see [Actual native/mark bridge seed](<small-period-native-mark-seed.md#proof-section-1>). The result required is...

$$
\begin{gathered}
\kappa_0<\kappa_1<\kappa_2<\kappa_3<\mu<\theta_5
<\beta<\alpha<\zeta<\eta<\theta_6<\kappa_4,\\
\operatorname{crit}(f)=\operatorname{crit}(H)=\kappa_0,
\qquad\operatorname{crit}(g)=\kappa_3,\\
f(\kappa_0)=\kappa_3,\quad f(\kappa_1)=\theta_5,\quad f(\kappa_2)=\beta,\\
g(\kappa_3)=\beta,\quad g(\theta_5)=\alpha,\\
H(\kappa_0)=\beta,\quad H(\kappa_1)=\alpha,\quad
H(\kappa_2)=\zeta,\quad H(\kappa_3)=\eta,\quad H(\beta)=\theta_6.
\end{gathered}
\tag{2}
$$

$\zeta<\eta<\theta_6$ also directly comes from taking the $H$-image of $\kappa_2<\kappa_3<\beta$.

Within the original complement term

$$
X=e_*(j_{(3)}),\qquad \boxed{D_\beta=g(X)}.
\tag{3}
$$

Existing $\operatorname{crit}(X)=\kappa_0$,
$X(\kappa_0)=\kappa_3$, $X(\kappa_3)=\theta_5$：
The last formula uses $\kappa_3=e_*(\kappa_2)$ and $j_{(3)}(\kappa_2)=\kappa_3$. $g$ is fixed with $\kappa_0$, therefore

$$
\operatorname{crit}(D_\beta)=\kappa_0,\qquad
D_\beta(\kappa_0)=g(X(\kappa_0))=g(\kappa_3)=\beta.
$$

Also because $\beta=g(\kappa_3)$,

$$
\boxed{D_\beta(\beta)=g(X)(g(\kappa_3))
=g(X(\kappa_3))=g(\theta_5)=\alpha.}
\tag{4}
$$

Therefore, $D_\beta:\kappa_0\mapsto\beta\mapsto\alpha$ is a clearly real term, and it is not an abstract possessor based on a required finite point image.

## 2. Eight-row initialization

Points and addresses are denoted as follows:

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,\beta,\alpha,\eta,\theta_6),
\qquad 0,1,\ldots,9.
\tag{5}
$$

The implicit endpoint of the $i$ row is the address $i+1$. The address $7$ in the 8 row is marked.

$$
\begin{array}{c|c|c|c|c}
i&\text{core}&L&\text{implicit endpoint}&\text{actual owner}\\\hline
1&(0,1)&1&2&j\\
2&(0,1,2)&1&3&j\\
3&(0,1,2,3)&2&4&K\\
4&(0,1,2,3,4)&2&5&K\\
5&(0,1,2,3,5)&3&6&f\\
6&(0,6)&1&7&D_\beta\\
7&(0,1,3,6,7)&3&8&H\\
8&(0,1,3,6,7^*,8)&3&9&H
\end{array}
\tag{6}
$$

Each row is paired in steps, exactly consisting of (2), (4) or the original $j,K$ point images. For example, the three sides of the 5 row are
$f(\kappa_0)=\kappa_3$, $f(\kappa_1)=\theta_5$, $f(\kappa_2)=\beta$.
In the 7 behavior of the $H$, there are three sides in the $\kappa_0,\kappa_1,\kappa_3$ source; in the 8 row, there is an additional $H(\beta)=\theta_6$. The owner of all rows equals the point corresponding to the first address.

In the 8 line, the source marked with $7$ is located at address $1$: its position is the 5 item, $L=3$. Therefore, the paired source is the 2 item of core. The trace is $(7,1)$, and the last owner is the $H$ in the 7 line. The 8 line also uses the exact same $H$, so the owner identity of this direct seam is truly equal, independent of any unverified truncation. In particular, the marked source $1$ is strictly greater than the first address $0$.

## 3. The first native packet is {2}

Adopting the local original rule the pinned original `iblp.py` in `SOURCE_MANIFEST.json`: For rows whose core length does not exceed $2L$, take $p=A[-L-1]$, $a=A[-L]$, and along $\delta(i)=A_i[-2]$ to collect the source points that are strictly greater than $p$ after the first hop.

In the 1-6 row, no packages are generated: the 2 and 4 rows are too long and were skipped; the first skip for the remaining rows does not exceed the threshold. In the 7 row, the core is $(0,1,3,6,7)$, $L=3$, therefore

$$
p=1,\qquad a=3,\qquad \delta(3)=2>1,\qquad\delta(2)=1.
$$

Therefore

$$
\boxed{\text{native packet}=(2).}
\tag{7}
$$

The source corresponds to $\kappa_2$, its true image is $H(\kappa_2)=\zeta$, and also $\alpha<\zeta<\eta$. Therefore, between the original addresses $7$ and $8$, $\zeta$ is inserted. The new point table is as follows:

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,
\beta,\alpha,\zeta,\eta,\theta_6).
\tag{8}
$$

The original completion is not a mid branch, because the original core length is $5<2L=6$. Calculated directly according to the code, the behaviors of the 7 and 8 positions after the replacement are as follows:

$$
\begin{array}{c|c|c|c|c}
7&(0,1,2,6,7)&3&8&H\\
8&(0,1,2,3,6,7^*,8)&4&9&H.
\end{array}
\tag{9}
$$

In the 7 row, there are three sides each, which are $H(\kappa_i)\;(0\le i\le2)$; in the 8 row, there are four sides, which are $H(\kappa_i)\;(0\le i\le3)$. Therefore, the implied endpoints of both rows are exactly $\zeta,\eta$, not just the original bridge row's sides remaining unchanged. The 1—6 row remains unchanged, and their implied endpoints do not cross the insertion position this time.

## The symbol 4. is used to propagate the same packet to subsequent lines.

The original line numbered 8 is changed to the line numbered 9; before marking processing, it is

$$
(0,1,3,6,7^*,9),\qquad L=3,\quad\text{implicit endpoint }10.
$$

The native is recorded as `record[7]=[2]`. At this point, the trace marked with $7$ is still $(7,1)$. Therefore, the mark completion indeed reads this record, adding the source address $2$ and the corresponding new address $8$, and increasing the step size to $4$. The result is as follows:

$$
\boxed{A_9=(0,1,2,3,6,7^*,8^*,9),\qquad L_9=4,\quad
\text{implicit endpoint }10=\theta_6.}
\tag{10}
$$

Its five sides are exactly

$$
H(\kappa_0)=\beta,\quad H(\kappa_1)=\alpha,\quad
H(\kappa_2)=\zeta,\quad H(\kappa_3)=\eta,\quad H(\beta)=\theta_6.
$$

Therefore, the original $H$ is still used, and there is no movement at the end.

The two completed markers, trace, are $(7,1)$ and $(8,2)$, corresponding to the owner in the 7 and 8 rows, which are both true $H$. Both have a source address $1,2$ that is positive and strictly greater than the initial address $0$. This is not a degenerate propagation that occurs due to zero source markers.

At this point, the new rows with the 7 and 8 indices, as well as the final row with the 9 index, have been saturated with native elements: their $(p,a)$ indices are respectively $(1,2),(2,3),(3,6)$, and the first jumps are respectively $1,2,0$, not exceeding the threshold. The actual scanning, from left to right, skipping the newly native-inserted rows, ends here.

## 5. Precise conclusions and unfinished parts

This finite seed has all actual owners, a non-empty native package has occurred, and the same package has been propagated along the positive source markers to subsequent lines; all newly added lines and implied endpoints have been verified, and the end still lies below $\kappa_4$.

It has not yet been proven that all subsequent replication addresses are defined, that arbitrary number of rounds of completion maintain the same semantic structure, that the seed is reachable from the original top, or that it provides a unified computational lower bound that surpasses BMS in structure. In particular, a successful native/mark scan does not replace the closure proof of subsequent replication and marking filtering.

Finite certificates (historical reference: `ordinary_l3_native_mark_seed_certificate.py`) actually construct $D_\beta$, verify the eight lines of initialization, then directly call the original code for a scan, and verify the final nine lines and all markers. The program is set to 10 seconds, 20 line limit; it does not run down to nothing, nor does it execute unbounded M searches.
