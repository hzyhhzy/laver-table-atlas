# Generate the next round of BMS rows using BMS descent length. · [中文版](bms-height-feedback.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

This version retains the three lines of feedback from the initial edition. The subsequent [Root-down feedback proof](<root-lowered-bms-feedback.md>) have been freed from their internal restrictions and logarithmic losses, resulting in $q(5)>D(D(h)+2)$, which covers all the available lines that were previously used. The end-point obstacles related to the direct use of $E$ still hold, but they are no longer a hindrance to the current approach.

Under the assumption of I3 and the realizability and unified front insertion lemma proven in this project, there exists a strict nested lower bound:

$$
\boxed{
q(5)>D_2(R_H),\qquad
H=\left\lfloor\log_2 D_2(R_3)\right\rfloor+2,
\quad R_h=(0^h)(1^h)(1^h).
}
\tag{1}
$$

The parentheses here represent the columns of BMS, and $h$ represents the number of rows; $D_2$ represents the total number of times a parent table is reset to a new $[2]$ until it becomes empty, which is equivalent to the number of times the original BM4 is reset to $[1]$. $q(5)$ is the Laver table order parameter for the first occurrence of the first row period reaching 32, and it is not the number of elements in the table. All embeddings, critical points, and witnesses belong to the same fixed $\operatorname{Iter}(j)$.

The formula (1) effectively uses the result of a single BMS descent as the number of rows for the next round, with the cost being a single binary logarithm. This initial scheme only provides three input rows and does not prove that the formula (1) itself is stronger than the lower bound of the previous $g^{258}(1)+2$ rows. Subsequent stronger conclusions come from different feedback embeddings and root-down chains, rather than directly assuming the endpoint conditions that have not been proven in this paper.

For the finite algebra part, see bms_height_feedback_certificate.py (Historical reference: `bms_height_feedback_certificate.py`). The following universal theorems are derived from written proofs and are not to be replaced by this procedure.

## Restoring chains with common roots from the number of critical points

Write the enumeration of critical points where $\gamma_0<\gamma_1<\cdots$ is the critical point of $\operatorname{Iter}(j)$. From [Dougherty's Second Theorem 3.1(c)](https://arxiv.org/pdf/math/9503204), for each natural number $s$,

$$
a_s=j_{(2^{2^s}-1)}:
\gamma_0\longmapsto\gamma_{2^s}\longmapsto\gamma_{2^{s+1}}.
\tag{2}
$$

Therefore, $a_0,\ldots,a_{m-1}$ explicitly testifies

$$
(\gamma_0,\gamma_1,\gamma_{2^m})
\quad\text{is }m\text{-lined}.
\tag{3}
$$

In other words, their common critical point is $\gamma_0$, and the chain passes through points with the subscript $1,2,4,\ldots,2^m$ in sequence.

If $r\ge2^m$, it is also possible to raise the endpoint to $\gamma_r$. When there is a strict inequality, take the critical point as $\gamma_{2^m}$, embed it into $B$ that sends it to $\gamma_r$, and change the last segment to $B(a_{m-1})$. Such a $B$ can be given by the finite composition of subsequent critical points; It fixes the first two points of that segment, so the remaining chains remain unchanged.

Conversely, the critical point counting lemma for linedness states that if $(\gamma_0,\gamma_1,\gamma_r)$ is $m$-lined, then $r\ge2^m$. See [Lemma 2.5](https://arxiv.org/html/2501.06733v5#S2). Therefore, for $r\ge2$, the maximum chain length of this specific triplet is exactly $\lfloor\log_2 r\rfloor$. This does not imply that the common root and starting point can be changed at will.

## Endpoint conditions required for feedback

Using the notation from [Unify the front-end insertion](<../iblp-laver-bms-20261013/lined-front-insertion.md>):

$$
K=j_{(11)},\qquad \mu=\theta_4,
\qquad L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7,
\qquad E=L_3(K).
$$

The definition of $E$ is an application, not a regular composition. Application points are given by identity equations and known points.

$$
\begin{aligned}
E(\gamma_0)&=E(\kappa_0)=\kappa_2,\\
E(\gamma_1)&=E(\kappa_1)=\theta_6,\\
E(\kappa_2)&=L_3(\mu),\\
E(L_3(\mu))&=L_3(K(\mu))
 =L_3(\theta_6)=\theta_7<\kappa_4.
\end{aligned}
\tag{4}
$$

**Feedback Lemma.** assumes $h\ge3$, with a closed compatible group that has a high $h$ level already available. The closure is a critical point $C$, and it additionally satisfies

$$
E(C)<\kappa_4.
\tag{5}
$$

Let $M=\lfloor\log_2 D_2(R_h)\rfloor$, we can get

$$
q(5)>D_2(R_{M+2}).
\tag{6}
$$

The closed compatible group **Proof.** provides a realization for $R_h$. By [With expansion and column deletion counting](<../iblp-laver-bms-20261013/ribbon-initialization.md>), if $C=\gamma_r$, then

$$
D_2(R_h)<r.
$$

Therefore, $2^M\le D_2(R_h)<r$, and thus $\gamma_{2^M}<C$. Taking the entire chain of (3) under the action of $E$-like, we obtain

$$
(\kappa_2,\theta_6,E(\gamma_{2^M}))
\quad\text{is }M\text{-lined},
$$

Its endpoints are strictly below $E(C)<\kappa_4$. The unified front insertion lemma transforms this chain into a closed compatible group with a height of $M+2$, and the closure remains strictly below the endpoints of the aforementioned chain. Using the implemented column deletion count again, along with $q(5)=F(4)+1$, we obtain (6). Proof complete.

These two simulations each compute a complete descent of a determined BMS seed. The number of iterations of M is not hidden in the definition of the fundamental sequence; nor is the finite number of critical points considered as a substitute for some ordinal embedding.

## The three-line input satisfies the additional endpoint conditions.

Take the closed group of [Two-layer initialization](<../iblp-laver-bms-20261013/short-terminal-initialization.md>), and seal it as $\rho<\theta_6$. Define

$$
Q=E(j),\qquad T=Q(j_{(10)}).
$$

Given (4),

$$
Q:\kappa_2\longmapsto\theta_6\longmapsto E(\kappa_2).
\tag{7}
$$

This is a chain that can be inserted at the front end. After one insertion, a closed and compatible group with a height of 3 is obtained, and the sealing is...

$$
C_3=T(\rho).
$$

Due to $j_{(10)}(\kappa_2)=\mu<\theta_6$,

$$
\begin{aligned}
C_3
&<T(\theta_6)\\
&=Q(j_{(10)})(Q(\kappa_2))\\
&=Q(\mu)\\
&<Q(\theta_6)
 =E(\kappa_2)=L_3(\mu).
\end{aligned}
\tag{8}
$$

Therefore

$$
\boxed{E(C_3)<E(L_3(\mu))=\theta_7<\kappa_4.}
\tag{9}
$$

This verifies the key additional condition of the feedback lemma. Substituting $h=3$ into (6) yields (1). Here, instead of using the old three lines to initialize the thicker seal $\theta_7$, a new three-line implementation is used, which results in a stronger upper bound (8).

## One cannot rely solely on the upper bounds of old endpoints for repeated feedback.

The construction of the previous eighteen lines and higher numbers gives $C_h<\theta_7$. It does not automatically yield (5). In fact, the following general inference is incorrect:

$$
C<\theta_7\quad\Longrightarrow\quad E(C)<\kappa_4.
$$

To clarify this point, take $\tau=E(\theta_6)=L_3(\theta_5)$. Since $\theta_5<\theta_6$ already exists, $\tau<\theta_7$ is also present. On the other hand, from $K(\theta_5)=\theta_7$,

$$
E(\tau)=L_3(\theta_7).
$$

In the initialization, $L_3=A(j_{(2)})$ and $A(\kappa_3)=\theta_7$ are set, while $j_{(2)}(\kappa_3)=\kappa_4$ is set. Therefore

$$
E(\tau)=L_3(A(\kappa_3))=A(\kappa_4)\ge\kappa_4.
\tag{10}
$$

This only negates the use of the rough boundary $C<\theta_7$ to ensure feedback security, and does not deny that specific closures with a larger number of rows may satisfy (5).

## Endpoint conditions of the old scheme and subsequent alternatives

If you still insist on embedding the feedback in $E$ from this article, and replace the inner layer with at least eleven lines that require additional proof $E(C_h)<\kappa_4$, then we can obtain the desired result.

$$
q(5)>D_2\!\left(R_{\lfloor\log_2 D_2(R_h)\rfloor+2}\right).
$$

This additional condition has not yet been proven for the original high row number constructions. In the future, we will use $P=L_3(f)$ and connect it with two descending root chains, using only the existing $C_h<\tau=E(\theta_6)$. This will lead to stronger conclusions without logarithmic losses. Therefore, we no longer consider proving this old condition as a necessary step.

It is also possible to replace the feedback embedding: If $E'$ satisfies $E'(\gamma_0)=\kappa_2$, $E'(\gamma_1)\ge\theta_6$, and $E'(C_h)<\kappa_4$, then the same proof still holds. It is necessary to prove these conditions separately; it is not sufficient to simply compare the critical points of each embedding.

## Finite verification

`bms_height_feedback_certificate.py` verifies the actual application items, compatible edges, membership truncation, and (8)—(9) for the three rows of entries. This verification is passed, and we retain 64 names, 112 embedding items, and 870 point images records, which took approximately 2 seconds. The program does not expand the $D_2(R_3)$ values, defaults to a 35 second time limit, and continues to use the protection for the number of points, items, and facts.

`feedback_cap_probe.py` checks whether the original sixteen-segment input ending with $x_{16}$ meets a stronger sufficient condition $E(E(x_{16}))<\kappa_4$. This time, the result is UNKNOWN: the existing finite relation has not been proven or negated for this comparison. Neither the checks inserted once nor twice have determined $E(C_4)<\kappa_4$. These uncertain results are not considered counterexamples.

The above numerical records describe only the scale of the certificate. The mathematical basis for the formula (1) is (2)—(9) and the cited universal lemma; its axiom conditions remain I3, and it has not been claimed to have been formalized to Lean.
