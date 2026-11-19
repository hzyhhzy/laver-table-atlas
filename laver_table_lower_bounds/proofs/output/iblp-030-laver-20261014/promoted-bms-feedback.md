# Two BMS row feedback under the same Laver cycle threshold · [中文版](promoted-bms-feedback.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Under the assumption of I3, the definition follows that of [First round of feedback](<root-lowered-bms-feedback.md>).

$$
D(h)=D_2((0^h)(1^h)(1^h)),\qquad T(h)=D(h)+2,
\qquad H_0=g^{258}(1)+2,\quad g(n)=n2^n.
$$

Here, $h$ represents the number of BMS rows; $D_2$ represents the number of times the parent table's new index is taken from $[2]$ to zero, which is equal to the number of times the original BM4 is taken from $[1]$. The number of rows can be fed back for another iteration to obtain the result.

$$
\boxed{q(5)>D(T(T(h)))=D\bigl(D(D(h)+2)+2\bigr)
\qquad(3\le h\le H_0).}
\tag{1}
$$

Both feedbacks occurred within the fixed $\operatorname{Iter}(j)$, and the seal was still lower than $\kappa_4$ in the end. This is not a conclusion based on arbitrary feedbacks, nor has a Hardy lower bound for the original IBLP $I[0][3][0]$ been established.

## Feedback lemma allowing the movement of starting points

It is said that $(P,a,b,c)$ satisfies the conditions of this lemma, which means that

$$
\begin{gathered}
\theta_6\le a<b<c<\kappa_4,\qquad
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c,\\
(\kappa_2,a,b)\text{ is 2-lined}.
\end{gathered}
\tag{2}
$$

If a closed compatible group with height $h\ge3$ has a closure of $C<b$, then there exists a closed compatible group with height $T(h)$ whose closure is strictly less than $c$.

The proof is the same as the first round, but allows $a>\theta_6$. Let $N=D(h)$, $m=\lfloor\log_2N\rfloor$. The implementation of the column deletion count gives $\gamma_N<C$. Dougherty's standard chain is $m$-lined $(\gamma_0,\gamma_1,\gamma_{2^m})$. Taking it as a $P$-image, we get $m$-lined $(a,b,Z)$, where

$$
Z=P(\gamma_{2^m})<P(C)<P(b)=c.
$$

Multiplying a two-segment chain with (2) gives a $(\kappa_2,a,Z)$ chain of $2^{m+1}>N$ segments. Contracting the endpoints to the $N$ segment, and then using [Unify the front-end insertion](<../iblp-laver-bms-20261013/lined-front-insertion.md>), we obtain a group with a high degree of $N+2=T(h)$, and a seal that is lower than $Z<c$. By uniformly inserting the originally allowed starting point $a\ge\theta_6$, no new, unproven insertion rules are added here.

A convenient transport condition is as follows. If $H$ fixes $\kappa_2$, and

$$
c\le H(b),\qquad H(c)<\kappa_4,
\tag{3}
$$

Then

$$
\bigl(H(P),H(a),H(b),H(c)\bigr)
\tag{4}
$$

It also satisfies (2). The entire two-chain is taken as the image of $H$; $H$ fixes $\gamma_0,\gamma_1,\kappa_2$, so the equality of the three points' images is derived from the application identity. Moreover, the output of the first round is lower than $c\le H(b)$, allowing for the input of the second round. The condition (3) is the actual endpoint budget that needs to be checked, and cannot be automatically derived from $c<\kappa_4$.

<a id="proof-section-2"></a>

## A comparison that is stronger than the original endpoint bounds.

Still write $K=j_{(11)}$, $\mu=\theta_4$, let

$$
\nu=j_{(9)}(\gamma_3),\qquad \theta_8=j_{(9)}(\kappa_3).
$$

It is necessary to prove

$$
\boxed{\theta_7<\nu<\theta_8<\kappa_4.}
\tag{5}
$$

The last two items come from strict monotonicity and the existing $\theta_8<\kappa_4$. The first item can be directly deduced from membership truncation. The previous five-layer finite certificates (historical reference: `five_row_certificate.py`) also used this comparison.

To avoid confusion with the column height function $D$, the following auxiliary embeddings are denoted as $V,A,B,Q$:

$$
V=j_{(10)}(j_{(10)}),\quad
A=j_{(9)}(j_{(3)})=V(j_{(10)}),\quad
B=V(j),\quad Q=j_{(10)}(K).
$$

The LD identity provides

$$
Q=V(K)=A(B).
\tag{6}
$$

The equal sign here represents an identity for the application term, not an embedding based on finite point images. From $\operatorname{crit}(V)=\kappa_2$, we have $B\equiv_{\kappa_2}j$. At the same time.

$$
A(\kappa_1)=\mu,\qquad A(\kappa_2)=\nu.
$$

After the transport truncation, (6) yields $Q\equiv_\nu A(j)$. Because of $\kappa_3<\mu=A(\kappa_1)$.

$$
A(j)(\kappa_3)<A(j)(A(\kappa_1))
=A(\kappa_2)=\nu.
\tag{7}
$$

Therefore, $Q(\kappa_3)=A(j)(\kappa_3)<\nu$ can be read strictly below the truncation point. On the other hand, the $K\equiv_\mu j\circ j$ transport in the 5 section of Dougherty's first paper is

$$
Q=j_{(10)}(K)\equiv_{\theta_8}K\circ K.
$$

Using the known $K(K(\kappa_3))=\theta_7<\theta_8$, we obtain $Q(\kappa_3)=\theta_7$. Combining this with (7) proves (5). This derivation only uses the initialized point images and truncation rules that have been established; see [Dougherty's original text](https://arxiv.org/pdf/math/9205202) for the source.

## Transport round one feedback

The first round has been constructed.

$$
P=L_3(f),\qquad a=\theta_6,\qquad
b=\tau=L_3(\theta_5),\qquad c=\theta_7.
$$

It satisfies (2), and $\mu<\theta_6<\tau<\theta_7$. Now take

$$
\boxed{H=j_{(9)}(j_{(4)}).}
\tag{8}
$$

From $j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3$,

$$
\operatorname{crit}(H)=\mu,\qquad H(\mu)=\nu,\qquad H(\nu)=\theta_8.
\tag{9}
$$

Therefore, $H$ fixes $\kappa_2$. Using (5) and $\mu<\tau$, it can be obtained that

$$
\theta_7<\nu=H(\mu)<H(\tau),
\qquad H(\theta_7)<H(\nu)=\theta_8<\kappa_4.
\tag{10}
$$

This is precisely (3). For any input with a height of $h\le H_0$, the first round yields groups with a height of $T(h)$, and the groups with a lower height than $\theta_7$ are sealed. In the second round, using (4), groups with a height of $T(T(h))$ are produced, and those with a lower height than $H(\theta_7)<\kappa_4$ are sealed. The implemented counting then yields (1).

Due to $D(n)\ge n+3$, the new lower bound also strictly exceeds the first round:

$$
D(T(T(h)))\ge D(T(h))+5>D(T(h)).
$$

It is not necessary to assume that the length of the decrease of a fixed index is monotonous for the comparison of general ordinals.

## Verifying the distance from the original IBLP goals

promoted_feedback_certificate.py (Historical reference: `promoted_feedback_certificate.py`) performs a finite algebraic verification on the two segments of (5)—(10) and the transport after that. This run was successful, taking approximately 1.8 seconds. There were 65 names, 120 embedding items, and 910 point images recorded. There is a limit of 35 seconds and the maximum number of names, items, and facts that can be inherited. It does not calculate $D(h)$, does not enumerate the complete descent of the BMS, and does not consider finite tests as proofs for general feedback lemmas.

The two rounds of construction only provide (1), without specifying the witnesses required for each original IBLP successor expansion. It is particularly inappropriate to refer to the feedback from either round or any fixed round as a $I[0][3][0]$ level of growth. To achieve the overall goal, it is still necessary to replicate the original rules and quantitatively simulate the preservation endpoint process, or to prove that another implemented process dominates the clear growth function of the original rules.
