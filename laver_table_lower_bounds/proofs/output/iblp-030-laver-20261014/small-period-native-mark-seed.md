# A native/mark seed with actual owners · [中文版](small-period-native-mark-seed.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Under ZFC + I3, fix the original $\operatorname{Iter}(j)$. Here, we provide a clear finite application of $H$, which satisfies

$$
\operatorname{crit}(H)=\kappa_0,\quad
H(\kappa_0)=t>\kappa_3,\quad H(\kappa_2)=v,\quad H(t)=E<\kappa_4.
\tag{1}
$$

It does not treat these equations as new assumptions, nor is there a need to search for a suitable possessor. This $H$ already appears in the original three-line initialization: it is precisely the original $r_*$.

<a id="proof-section-1"></a>

## 1. actually refers to a finite number of elements.

Let $K=j_{(11)}$, and continue as before

$$
\theta_0=\kappa_0,\quad\theta_1=\kappa_1,\quad
\theta_2=\kappa_2,\quad\theta_3=\kappa_3,
$$

$$
\kappa_3<\mu=\theta_4<\theta_5<\theta_6<\theta_7<\kappa_4,
\qquad K(\theta_i)=\theta_{i+2}\quad(0\le i\le5).
\tag{2}
$$

This is the existing finite initialization of $j,K$. Definition

$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K),
$$

$$
\boxed{g=f(K),\qquad H=g(f).}
\tag{3}
$$

The entire text contains 'application' instead of ordinary composition. The critical points are calculated by $\operatorname{crit}(u(v))=u(\operatorname{crit}(v))$.

The previous limited derivations have provided

$$
\operatorname{crit}(e_*)=\kappa_2,\qquad
e_*(\kappa_2)=\kappa_3,\quad
e_*(\kappa_3)=\theta_5,\quad e_*(\theta_5)=\theta_6,
\tag{4}
$$

and

$$
\operatorname{crit}(f)=\kappa_0,\qquad
f(\kappa_0)=\kappa_3,\quad f(\kappa_1)=\theta_5,
\quad f(\theta_5)=\theta_6.
\tag{5}
$$

(4)—The item-by-item derivation of (5) has been fully listed in [Short Transport Lemma, Section 1](<small-period-endpoint-Sf.md#proof-section-1>); they only use (2), application point-like identities, and fixities.)

Define three named critical points

$$
\alpha=e_*(\mu),\qquad \beta=f(\kappa_2),\qquad \zeta=f(\mu).
\tag{6}
$$

Because $\kappa_3=e_*(\kappa_2)$

$$
f(\kappa_3)=e_*(K)(e_*(\kappa_2))
=e_*(K(\kappa_2))=e_*(\mu)=\alpha.
\tag{7}
$$

By strict monotonicity,

$$
\boxed{\kappa_3<\theta_5<\beta<\alpha<\zeta<\theta_6<\kappa_4.}
\tag{8}
$$

Specifically, the $f$-images of $\kappa_1<\kappa_2<\kappa_3$ give $\theta_5<\beta<\alpha$, and the $f$-images of $\kappa_3<\mu<\theta_5$ give $\alpha<\zeta<\theta_6$. These points are all real critical points in the same ambient algebra, and they are not merely ordinal numbers named arbitrarily to make the diagram orderly.

## All necessary point images of 2. H

First, $\operatorname{crit}(g)=f(\kappa_0)=\kappa_3$, so $g$ fixes $\kappa_0,\kappa_1,\kappa_2$. By the application identity,

$$
\begin{aligned}
g(\kappa_3)&=g(f(\kappa_0))=f(K(\kappa_0))=f(\kappa_2)=\beta,\\
g(\theta_5)&=g(f(\kappa_1))=f(K(\kappa_1))=f(\kappa_3)=\alpha,\\
g(\beta)&=g(f(\kappa_2))=f(K(\kappa_2))=f(\mu)=\zeta,\\
g(\alpha)&=g(f(\kappa_3))=f(K(\kappa_3))=f(\theta_5)=\theta_6.
\end{aligned}
\tag{9}
$$

Because $H=g(f)$

$$
\operatorname{crit}(H)=g(\kappa_0)=\kappa_0.
$$

By substituting the three low points where $g$ is fixed, we obtain

$$
\begin{aligned}
H(\kappa_0)&=g(f(\kappa_0))=g(\kappa_3)=\beta,\\
H(\kappa_1)&=g(f(\kappa_1))=g(\theta_5)=\alpha,\\
H(\kappa_2)&=g(f(\kappa_2))=g(\beta)=\zeta.
\end{aligned}
\tag{10}
$$

Finally, $\beta=g(\kappa_3)$, therefore

$$
H(\beta)=g(f)(g(\kappa_3))=g(f(\kappa_3))=g(\alpha)=\theta_6.
\tag{11}
$$

So take

$$
\boxed{t=\beta,\qquad v=\zeta,\qquad E=\theta_6}
\tag{12}
$$

To satisfy (1), and additionally to obtain $H(\kappa_1)=\alpha\in(t,v)$.

## The precise interface for the target seed is marked as 3..

The name of the point table is taken from...

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,t,v,E),
$$

The addresses are respectively $0,1,2,3,4,5,6$. The same $H$ implements:

- core $(0,2,4)$, step size $2$, implicit endpoint $5$: The relationship is
  $H(\kappa_0)=t$, $H(\kappa_2)=v$; 
- core $(0,2,4,5)$, step size $2$, implicit endpoint $6$: additional addition
  $H(t)=E$.

Therefore, the shared seams in these two lines are implemented by truly identical owners, not just relying on finite point similarities. If the native operation indeed requires inserting the corresponding image of the source $\kappa_1$, then this image is precisely $\alpha$, and there already exists a strict position $t<\alpha<v$. The interpolated single bridge line

$$
(\kappa_0,\kappa_1,\kappa_2,t,\alpha,v),\qquad L=3,
\quad\text{implicit endpoint }E
$$

It is still achieved by $H$, because its four pairings are precisely (10)—(11).

Here, we first complete the required owners and single bridge point image interfaces. In the next section, we will fill in the actual `owner` of the `3` row; however, whether the actual `native`/`mark guard` precisely selects this source package, and whether the implicit endpoints of the remaining rows remain after insertion, must be verified by the caller according to the complete state rules. These syntax conditions that have not been checked here are not packaged as proven in this document.

### 3.1 Complete the first row that was previously unassigned: 3

In the specific point table above, the 3 row is core $(0,3)$, the step size is $1$, and the implicit endpoint is $4$. It is not suitable to copy it as a non-main zero row; if copied, the first address $0$ would need to be sent to the correct address, and the new row would then require a true owner. It can be explicitly completed here without changing the point table or other rows.

Let $j_{(2)}=j(j)$, $j_{(3)}=j_{(2)}(j)$, and define

$$
X=e_*(j_{(3)}),\qquad R=f(j_{(2)}),\qquad
\boxed{W=R(X)=f(j_{(2)})(e_*(j_{(3)})).}
\tag{13}
$$

Standard small dot like is

$$
j_{(2)}(\kappa_1)=\kappa_2,\qquad
j_{(3)}(\kappa_0)=\kappa_2,\qquad j_{(3)}(\kappa_2)=\kappa_3.
$$

$e_*$ is fixed by $\kappa_0$, and also by $e_*(\kappa_2)=\kappa_3$, so

$$
\operatorname{crit}(X)=\kappa_0,\quad
X(\kappa_0)=e_*(\kappa_2)=\kappa_3,
\quad X(\kappa_3)=e_*(j_{(3)}(\kappa_2))=\theta_5.
\tag{14}
$$

On the other hand,

$$
\operatorname{crit}(R)=f(\kappa_1)=\theta_5,\qquad
R(\theta_5)=f(j_{(2)}(\kappa_1))=f(\kappa_2)=\beta.
\tag{15}
$$

$R$ is fixed by $\kappa_0,\kappa_3$, therefore

$$
\boxed{\operatorname{crit}(W)=\kappa_0,\quad
W(\kappa_0)=\kappa_3,\quad W(\kappa_3)=\beta.}
\tag{16}
$$

Thus, all five elements of the seed can be fully provided to the owner:

$$
\begin{array}{c|c|c|c|c}
\text{row number}&\text{core}&L&\text{implicit endpoint}&\text{owner}\\\hline
1&(0,1)&1&2&j\\
2&(0,1,2)&1&3&j\\
3&(0,3)&1&4&W\\
4&(0,2,4)&2&5&H\\
5&(0,2,4,5)&2&6&H
\end{array}
\tag{17}
$$

The marker for the last line, $4$, is retained separately; the junction of the two lines, $H$, remains truly the same owner. Each line is paired with points that correspond to steps, and the critical points have been verified. Therefore, this seed no longer relies on the weak semantics that "the zero line is never used as an owner"; if we take the entire line 3 as the actual $Q$-image, then the existing $Q(W)$ can be used. This does not yet equalize all the renumbering and completion conditions that have been checked for any subsequent step.

### 3.2 The next short [2] requires two replicators to own it.

Let $\eta=H(\kappa_3)$. From $\kappa_2<\kappa_3<\beta$ and (10)—(11),

$$
\beta<\alpha<\zeta<\eta<\theta_6.
\tag{18}
$$

Using the same replicator $H$, the owners of the two new rows take the actual terms.

$$
J_6=H(j),\qquad W_7=H(W).
$$

Both critical points are $H(\kappa_0)=\beta$. According to the application point image identity,

$$
\boxed{J_6:\beta\mapsto\alpha\mapsto\zeta\mapsto\eta,\qquad
W_7:\beta\mapsto\eta\mapsto\theta_6.}
\tag{19}
$$

The first one is the $H$-image of $j:\kappa_0\mapsto\kappa_1\mapsto\kappa_2\mapsto\kappa_3$. The second one is the $H$-image of the just-completed $W:\kappa_0\mapsto\kappa_3\mapsto\beta$. Especially for $W_7(\eta)=H(W(\kappa_3))=H(\beta)=\theta_6$, this replication did not lose the end budget.

At the point table

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\beta,\alpha,\zeta,\eta,\theta_6)
$$

In the 6 row, the core $(4,5,6)$, $L=1$, and implicit endpoints $7$ are implemented by $J_6$; in the 7 row, the core $(4,7)$, $L=1$, and implicit endpoints $8$ are implemented by $W_7$. This is precisely the owner that was missing when the old unassigned row head addresses changed from $0$ to the positive address $4$. There are now clear items, and the zero-port exception is no longer applicable.

## 4. finite verification

small_period_native_mark_seed_certificate.py (Historical reference: `small_period_native_mark_seed_certificate.py`) calls upon the existing `three_row_certificate.py` true application construction, and directly asserts the pairing of (8), (10), (11) with two bridge rows of length 2, and single bridge rows of length 3 after interpolation; it also constructs (13) of $W$, checks all rows of (16) and (17). The certificate also constructs $H(j),H(W)$, checks (19), and the next replication of the 6, 7 rows. It does not run M, does not enumerate BMS descent, nor introduces an abstract owner that is not specified.
