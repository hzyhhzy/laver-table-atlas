# Marked completion preserved by the prefix of linedness · [中文版](lining-prefix-cutoff.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Fixing the same I3 to be embedded in $j$, all owners are in the embedding algebra it generates. The following proof demonstrates that the actual two relocations result in eight linedness points, which share the first seven points with a construction using only $j_{(13)}$. Therefore, it can be clearly concluded that there are five sources that lie between $\kappa_3$ and $\mu=\theta_4$.

These points can be used in the source interval of [Whole-block insertion lemma](<block-fan-insertion.md>), but the required compatible mappings and lower endpoint closures have not yet been constructed. The completed BMS initialization is still at the three-layer level.

## Truncated equivalence and term substitution

The mathematical research manuscript translates as follows: 

The membership truncation equivalence of Laver is denoted by $a\equiv_\delta b$. Each truncation point here is either a critical point or its image, thus it is an ordinal limit. The application of $a(b)$ and the composite $a\circ b$ are strictly distinguished from each other.

If $a\equiv_\delta b$, then in the same finite application term, $b$ is used to replace $a$, and the resulting embedding remains equivalent to $\delta$. This is a generalization of the dual-parameter contractive pair structure of the application. It does not claim that the application is monotonous with respect to the left parameter at every point. If one of the embeddings has an image on some ordinal that is strictly less than $\delta$, the two images are equal; this cannot be read as equal to a truncated bound. These properties come from [Dougherty, Chapter 5](https://arxiv.org/pdf/math/9205202).

According to this, there is a prefix lemma that applies to the construction of linedness. Suppose the owners of the two sets of constructions are $T_i(B)$ and $T_i(B_0)$, where $T_i$ is the same finite application item, $B\equiv_\mu B_0$, and the common critical point is $c$. If the standard construction satisfies

$$
x_i^0=T_i(B_0)(c)<\mu\qquad(0\le i<s),
$$

In the actual construction, the $x_i=T_i(B)(c)$ is identical to the one at each point. If the last point in the standard construction is precisely $\mu$, this lemma only retains the points before that point, and does not consider the actual last point as $\mu$.

## Specific prefixes for the eight testimonies

Let $K=j_{(11)}$, $\mu=\theta_4$. After the 32 step of marking is initiated, the last owner $F$ has a direct mark at the 3th point: the factor is at the 3th row, $K$, and the natural truncation boundary is at the original 4th point. Therefore

$$
F\equiv_\mu K.
\tag{1}
$$

The transporter of the first [Point-preserving relocation](<marked-prefix-rebase.md>) is $F(j)$, and the new second row's owner is

$$
B=F(j)(j)\equiv_\mu K(j)(j)=j_{(13)}=:B_0.
\tag{2}
$$

Fixing the linedness of two segments

$$
L=(\kappa_0;\ \kappa_1,\kappa_2,\kappa_3),
\qquad\text{owner }(j,j_{(3)}).
\tag{3}
$$

It is known that the critical sequence of $B_0$ starts with
$\kappa_0\mapsto\kappa_1\mapsto\kappa_3\mapsto\mu$.
Therefore, $B_0(L)$ is a witness of the two-segment $(\kappa_1,\kappa_3,\mu)$. From [Lemma 2.3](https://arxiv.org/html/2501.06733v5#S2), multiplying $L$ by $B_0(L)$ yields the $2\cdot2^2=8$ segment:

$$
\kappa_1=x_0<x_1=\kappa_2<x_2=\kappa_3
 <x_3<x_4<x_5<x_6<x_7<x_8=\mu.
\tag{4}
$$

In the same multiplication construction, using $B$ instead of $B_0$ yields the second actual relocation of the eight witnesses. The two sets of owners have the same application item template, so from (2) and the prefix lemma, the actual $x_0,\ldots,x_7$ is equal to (4) point by point. The actual last point is $B(\kappa_3)>\mu$, which is still less than $\kappa_4$; the standard endpoints that equal the truncated bounds have not been incorrectly read.

For ease of use in subsequent use, let

$$
H=B_0(j),\qquad A=B_0(j_{(3)}).
$$

Then the five intermediate points can be taken as

$$
\begin{aligned}
x_3&=H(\kappa_2)=j_{(14)}(\kappa_2),\\
x_4&=B_0(\kappa_2),\\
x_5&=A(\kappa_2),\\
x_6&=A(\kappa_3)=B_0(\gamma_3),\\
x_7&=A(H(\kappa_2)).
\end{aligned}
\tag{5}
$$

Here, $\gamma_3=j_{(3)}(\kappa_1)$. For example, the upper bound of the last point can be directly determined: $x_3<x_4=B_0(\kappa_2)$, and so on.

$$
A(x_4)=B_0(j_{(3)})(B_0(\kappa_2))
       =B_0(j_{(3)}(\kappa_2))
       =B_0(\kappa_3)=\mu,
$$

So, $x_7=A(x_3)<\mu$.

The finite algebra verification (historical reference: `lining_prefix_agreement_probe.py`) examined the application of term substitution, eight common points, two different terminal points, and strict interval relationships with five points. The highest number of owners is 300, and no descending process of any target magnitude is unfolded.

## The exact critical points with five points

The above five points can also be precisely distinguished as

$$
(x_3,x_4,x_5,x_6,x_7)
 =(\gamma_8,\gamma_{16},\gamma_{32},\gamma_{64},\gamma_{128}),
\qquad \mu=\gamma_{256}.
\tag{5a}
$$

Therefore, the nine points of the standard eight-segment testimony are as follows:

$$
\gamma_1,\gamma_2,\gamma_4,\gamma_8,\gamma_{16},
\gamma_{32},\gamma_{64},\gamma_{128},\gamma_{256}.
\tag{5b}
$$

Prove using [Dougherty, Article 2, Sections 7, 8](https://arxiv.org/pdf/math/9503204). Sections 8 give $j_{(14)}(\kappa_2)=\gamma_8$, $j_{(13)}(\kappa_2)=\gamma_{16}$, and

$$
A\restriction V_\mu
 =D\restriction V_\mu,\qquad D=j_{(2^{16}-2)}.
$$

Section 7 Theorem 7.2(c), along with the lemma 7.1 used in its proof, is presented.

$$
D(\gamma_i)=\gamma_{16i}\quad(1\le i\le16).
$$

Substitute $i=2,4,8,16$, and in combination with (5), we obtain (5a) and endpoints.
$A(\gamma_{16})=\gamma_{256}=\mu$.

Here, the symbol **Ordinary function restriction** is used. Entering $\gamma_i<\mu$ will allow the reading of the equation, and the output is allowed to be equal to $\mu$. This is different from the previous "output is strictly within the bounds" condition with membership truncation. It cannot be further asserted with $A(\mu)=D(\mu)$ by this restricted equation. Finite verification has checked both of these reading conditions, and no domain boundaries have been read.

## Why simply compressing linedness does not equal increasing the BMS layer

Let a sequence of witnesses satisfy

$$
\operatorname{crit}(e_i)=c,\qquad
e_i(c)=u_i,\qquad e_i(u_i)=u_{i+1},
\qquad c<u_0<\cdots<u_m.
$$

For adjacent segments of $a:c\mapsto u\mapsto v$ and $b:c\mapsto v\mapsto w$, the common combination is

$$
C=b(b)(a).
\tag{6}
$$

It gives $C:c\mapsto u\mapsto w$. But $\operatorname{crit}(b(b))=v$, so

$$
C\equiv_v a,\qquad C(\xi)=a(\xi)\quad(\xi<u).
\tag{7}
$$

The second equation can also be directly proven: $b(b)$ fixes both $\xi$ and
$a(\xi)<a(u)=v$.

Therefore, for each non-pre-antecedent with the same starting $u_0$, regardless of how it is bracketed, the repeated use of (6), ultimately owning $P$ always satisfies

$$
P\equiv_{u_1}e_0,\qquad P(u_0)\ge u_1.
\tag{8}
$$

For the merged trees, a simple induction can be applied: The new merged cut-off point is at least $u_1$, and the equivalent relationships that have been retained on the left side will not be weakened.

These compressed owners cannot form a highly pairwise compatible group with the first goal being $u_0$. If they can, then $K_1,K_2$ and some $U_2<u_0$ must be satisfied.

$$
K_2(U_2)=K_1(u_0).
$$

However, from (8), the left side equals $e_0(U_2)<u_1$, and the right side is at least $u_1$, which is contradictory.

This restriction applies only to the specific extraction method that starts with "the same linedness and standard merging." It does not exclude the use of completion, different source positions, different historical application items, or compatible blocks to increase the number of layers.

## Location where the dual-factor marker appears

After two actual relocations, take $E(2)$, then perform four short copies and completions. The specific items are verified (historical reference: `concrete_marked_packet_probe.py`) in sequence.
36. 36, 84, 116, 194 rows. The last state appears for the first time with 11 dual-factor markers
Examples belonging to different owners in 8; their traces are all $(84,36,1)$. If the owners in the 84th and 36th rows are respectively $A_*,B_*$, these markers provide a common natural certificate.

$$
F_i\equiv_{\theta_{85}} A_*\circ B_*.
\tag{9}
$$

The boundaries are indeed $A_*(\theta_{37})=\theta_{85}$, and they are not chosen arbitrarily as the next column. They share $F_i(\theta_0)=\theta_{37}$, $F_i(\theta_1)=\theta_{84}$, and have different points outside the boundaries.

These multi-factor relationships provide the specific objects that will be analyzed later, but the point images recorded so far have not yet formed new closed higher-level groups. The corresponding states of the parameter 8 include 1, 202 rows, and 263 instances of dual-factor markers; the previous 900 row diagnosis has just stopped before its occurrence. It is not possible to infer the number of 263 BMS layers from this count.

## Verification of truncation formula

In this diagnosis, it was found that there were two literature formulas whose transcription boundaries were too large, and they have been corrected. The correct form is as follows:

$$
j_{(14)}\equiv_{j_{(13)}(\kappa_2)}j(j_{(3)}),
\qquad
j_{(15)}\equiv_{j_{(14)}(\kappa_2)}j_{(2)}(j_{(3)}).
$$

It is not possible to elevate both bounds to $\mu$. The literature's equation chain uses different bounds for the equal sign, and the entire chain can only adopt the smaller bound that applies to them all. This correction only involves the newly added truncation diagnostics; the independent three-layer certificates do not use these two approximate formulas.
