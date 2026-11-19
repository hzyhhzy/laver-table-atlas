# pIBLP: Self-feedback and upper bound of periodic thirty-two for quantitative functions · [中文版](quant-self-feedback.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Assume ZFC + I3, and all actual embeddings are taken from the same $\operatorname{Iter}(j)$. Follow the current pIBLP rules: if the first complete copy of the address domain fails, the last line is deleted, without changing it to the longest valid prefix copy. Denote the nine actual seeds as $S$, and set them up.

$$
G(m)=f_{\rm PP}(S,m).
\tag{1}
$$

Here, $f_{\rm PP}$ is a recursive calculation of [Parent package finite parameter quantitative bridge](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.md>) in (3), not the FGH of pIBLP, nor a fixed total number of `[2]`. Existing quantitative bridges can self-reflect to obtain

$$
\boxed{q(5)>2^{G^{\circ3}(1)}.}
\tag{2}
$$

Along the existing BMS feedback long chain, it is also possible to obtain

$$
\boxed{q(5)>2^{G^{\circ(N+1)}(1)},\qquad
N=D(T(h)),\quad 3\le h\le C_{\rm line}+2.}
\tag{3}
$$

$D,T,C_{\rm line}$ uses the original definitions of [Feedback segment by segment along the long chain](<../iblp-030-laver-20261014/lined-feedback-corridor.md>), especially $T(h)=D(h)+2$. In the 4 section, we construct the completion of segment endpoints by using the adjacent critical points of the homology, to avoid extending the Qi lemma 2.11 beyond the scope of the same BLS. This proof focuses on the new numerical interface added to pIBLP; it does not prove that $G$ dominates the BMS feedback function $T$, thus not claiming that (2) or (3) exceed the best explicit lower bound for BMS–FGH.

## The accurate input for a finite-parameter quantitative bridge marked with 1.

The actual seed $S$ has the first three points as $(\kappa_0,\kappa_1,\kappa_2)$, and the cap is $\theta_6<\kappa_4$. It has an initial 1-linedness witness, which satisfies the conditions of ordinary row type, ActiveSat, proper marks, accurate traces, correct source of marks, and natural membership truncation. Its complete certificate can be found at [A Sat proof for nine-row seeds](<../iblp-030-laver-20261014/same-owner-L3-sat-closure.md>).

The form of quantitative bridges is as follows: For any valid actual realization of the same grammatical pattern, as long as the current first triple has a finite $m$-linedness witness, it also obtains the definiteness of that $G(m)$ call.

$$
(\text{first point},\text{second point},\text{cap})
\quad\text{of}\quad G(m)\text{-linedness}.
\tag{4}
$$

This allows for the sequential change of implementations and the current finite parameters. It does not require the original fixed triplet $(\kappa_0,\kappa_1,\kappa_2)$ to have arbitrarily large linedness at the same time.

## 2. Implementation of the image of the same grammatical pattern

Let $Q\in\operatorname{Iter}(j)$ be fixed at $\kappa_0,\kappa_1$. Take the embeddings of all named points, row owners, actual factor words of marks, and truncation bounds of $S$ at $Q$. Denote the resulting implementations as $Q(S)$. Its integer address, step size, and mask remain unchanged, so it is still a grammatical pattern $S$. Its first three points and cap are respectively

$$
(\kappa_0,\kappa_1,Q(\kappa_2)),\qquad Q(\theta_6).
\tag{5}
$$

All owners $Q(J_r)$ still belong to the original $\operatorname{Iter}(j)$, without re-generating the enumeration of critical points. The edges of the ordinary rows and critical points are maintained by the application point image identity; ActiveSat, proper, positive sources, and accurate traces all maintain the same conditions after integer addressing.

If a mark originally has a non-terminal word that is $W=J_{v_0}\circ\cdots\circ J_t$, the natural truncation boundary is

$$
\Delta(W)=(J_{v_0}\circ\cdots\circ J_{v_{d-2}})(\xi_{t+1}),
$$

The resulting words are taken as composites corresponding to the $Q(J_v)$, which in nature are precisely the $Q(\Delta(W))$. The membership truncation equivalence is transported along with the $Q$. Therefore, the marks maintain their actual natural truncation certificates, rather than merely retaining the symbol `*`.

The linedness of the first three points is witnessable to be redefined; the aforementioned row edges, marks, and their certificates do not depend on the identity of this witness. This is precisely the condition that allows quantitative bridges to be replaced with finite parameters.

## 3. Threefold self-composition of specific small windows

Continue to use the notation [First round of root reduction feedback](<../iblp-030-laver-20261014/root-lowered-bms-feedback.md>)

$$
b=K(j),\quad W=L_3(b),\quad
a=L_3(\mu),\quad \tau=L_3(\theta_5).
$$

There are existing actual point images and strict orders.

$$
\operatorname{crit}(W)=\kappa_2,\qquad
W(\kappa_2)=\theta_6,\quad W(\theta_6)=a,\quad W(a)=\tau,
\tag{6}
$$

$$
\kappa_2<\theta_6<a<\tau<\theta_7<\kappa_4.
\tag{7}
$$

Therefore, both $W$ and the ordinary composite $W\circ W$ fix the first two points. The third quantitative call is as follows: $W^2(S)$ indicates that all data are taken twice$W$-like, rather than the application item$W(W)$ acting on$S$.

| Practical realization | The first three points | cap | This parameter | The linedness of the first two points up to the cap |
| --- | --- | --- | --- | --- |
| $S$ | $(\kappa_0,\kappa_1,\kappa_2)$ | $\theta_6$ | $1$ | $G(1)$ |
| $W(S)$ | $(\kappa_0,\kappa_1,\theta_6)$ | $a$ | $G(1)$ | $G(G(1))$ |
| $W^2(S)$ | $(\kappa_0,\kappa_1,a)$ | $\tau$ | $G(G(1))$ | $G^{\circ3}(1)$ |

The input of each line is a witness of the output of the previous line, thus the call to definitiveness is established sequentially. It is not assumed in advance that $G$ is defined for all integers.

Write $\tau=\gamma_r$, where $\gamma_i$ enumerates the critical points of the same global algebra. The counting lemma for linedness of the same algebra is given as

$$
2^{G^{\circ3}(1)}\le r.
$$

Because $\tau<\kappa_4=\gamma_{q(5)-1}$, there is $r<q(5)-1$, hence we get (2).

### Why can't we repeat the same W indefinitely?

There is a definite fourth step of escape, which cannot be omitted simply by skipping the endpoint check. Based on $\theta_5=K(\kappa_3)$ and the application point image identity,

$$
b(\theta_5)=K(j)(K(\kappa_3))=K(j(\kappa_3))
=K(\kappa_4)\ge\kappa_4.
$$

Therefore

$$
W(\tau)=L_3(b)(L_3(\theta_5))
=L_3(b(\theta_5))\ge\kappa_4.
\tag{8}
$$

The fourth $W$-image implementation is the $W(\tau)$, which can no longer be used in the current $q(5)$ window. In the long-chain version, each segment is assigned a separate actual $Q_i$, eliminating this ineffective infinite repetition.

## The actual connection between any two critical points in the same algebra is denoted by 4..

Lemma 2.11 provides the required owner between two columns in a qualified BLS. It cannot be rephrased as "there exists an owner with a specified critical point and a specified image between any two critical points of the same $\operatorname{Iter}(j)$". A quantitative proof for the cut branch uses precisely the same two columns in the same BLS, as seen in [The original marked quantitative proof](<../../natural-mark-lemmas/marked_blp_proof.en.md>).

This article uses a more direct external fact to present the entire finite induction. As recorded in [At the beginning of Chapter 3 of the second article by Dougherty, page 10 of the PDF.](https://arxiv.org/pdf/math/9503204#page=10): Let $e_n=j_{(2^n)}$ be...

$$
\operatorname{crit}(e_n)=\gamma_n,\qquad
e_n(\gamma_n)=\gamma_{n+1}.
\tag{9}
$$

Here, $j_{(k)}$ is a left-combined application term of k in j, which is not a ordinary composite power. All $e_n$ belong to the same $\operatorname{Iter}(j)$.

For any finite integer $a<b$, define the actual application item

$$
L_{a,a+1}=e_a,\qquad
L_{a,b+1}=e_b(L_{a,b}).
\tag{10}
$$

Prove by finite induction on $b-a$

$$
\operatorname{crit}(L_{a,b})=\gamma_a,\qquad
L_{a,b}(\gamma_a)=\gamma_b.
\tag{11}
$$

The basic step is (9). In the inductive step, it's $a<b$, so $e_b$ fixes $\gamma_a$. The critical point formula for application gives

$$
\operatorname{crit}(e_b(L_{a,b}))
=e_b(\operatorname{crit}(L_{a,b}))=e_b(\gamma_a)=\gamma_a.
$$

Reading point images as identities at the same fixed points, there is

$$
e_b(L_{a,b})(\gamma_a)
=e_b(L_{a,b})(e_b(\gamma_a))
=e_b(L_{a,b}(\gamma_a))
=e_b(\gamma_b)=\gamma_{b+1}.
$$

This completes (11), and explicitly constructs each required connection without adding any common BLS assumptions. The Laver–Steel theorem has already listed all the critical points of the current algebra as $\gamma_n$ with finite indices. Therefore, for any current critical point $z=\gamma_a<u=\gamma_b$, we can choose $B=L_{a,b}$ to obtain $\operatorname{crit}(B)=z$, $B(z)=u$.

Specifically, if the last paragraph of a $m$-linedness is

$$
\operatorname{crit}(A)=\kappa_0,\quad
A(\kappa_0)=x,\quad A(x)=z,
\qquad \kappa_0<x<z,
$$

Then $B$ fixes $\kappa_0,x$. Replace the last owner with $B(A)$, and we have

$$
B(A)(\kappa_0)=x,\qquad B(A)(x)=u.
$$

All previous paragraphs remain unchanged, with the number of paragraphs still being $m$. If $z=u$, there is no need for replacement. Therefore, the $m$-linedness of $(\kappa_0,\kappa_1,z)$ can be extended to any larger homomorphic critical point $u$ without reducing the number of segments. What changes here is the separate carried witness of linedness, while the row owners or marks of $S$ remain unchanged.

## 5. along a finite-length chain composition G

Let there be a given actual finite chain

$$
\theta_6\le u_0<u_1<\cdots<u_N<\kappa_4,
\tag{12}
$$

$$
\operatorname{crit}(Q_i)=\kappa_2,\quad
Q_i(\kappa_2)=u_i,\quad Q_i(u_i)=u_{i+1}
\qquad(0\le i<N).
\tag{13}
$$

If there is already a $(\kappa_0,\kappa_1,z_i)$ with $M_i$-linedness and a $z_i\le u_i$, then extend it to $u_i$ through the explicit connection from the previous section. This is the first witness required to implement $Q_i(S)$. Quantitative bridges are provided.

$$
M_{i+1}=G(M_i),\qquad z_{i+1}=Q_i(\theta_6).
\tag{14}
$$

Because $\kappa_2<\theta_6\le u_i$, strict monotonicity gives

$$
u_i=Q_i(\kappa_2)<z_{i+1}
=Q_i(\theta_6)\le Q_i(u_i)=u_{i+1}.
\tag{15}
$$

Therefore, the output satisfies the input conditions for the next section. The first two points remain unchanged, and the natural certificates of marks are maintained by the 2 section. For finite $i$ induction, it is also proven that the definitions of each $G$ call are correct and (14). Finally, it is established that $G^{\circ N}(M_0)$-linedness, with no exceeding $u_N<\kappa_4$ at the end. Therefore,

$$
q(5)>2^{G^{\circ N}(M_0)}.
\tag{16}
$$

In particular, by first obtaining $M_0=G(1),z_0=\theta_6$ from the original $S$, we obtain the number of times of composition required for $N+1$ in (3).

[There is already a corridor proving the 4 section.](<../iblp-030-laver-20261014/lined-feedback-corridor.md>) For each $3\le h\le C_{\rm line}+2$, Provide the actual chain of (12)—(13). Its length is $N=D(T(h))$. Starting from the original promoter $S_{\rm prom}(a)>\theta_7>\theta_6$ The end is strictly below $S_{\rm prom}(\theta_7)<\kappa_4$. The promoter here is not the same object as the nine-line syntax seed $S$ in this article.

Each pair of $z_i<u_i$ represents a critical point in the current global algebra. Therefore, the 4 section provides actual $B_i$ for each pair. The length of these terms may be extremely long, but this is a finite construction applied to a finite set of integers. The construction is not included in the pIBLP as a step-by-step expansion, nor is it required to compute its complete text. As a result, all the connectivity conditions for (3) have been provided.

## The comparison between strict growth and the unconnected state of 6.

By inductive reasoning on the natural number potential used in quantitative bridging, it can be proven that each implemented call satisfies

$$
f_{\rm PP}(P,m)\ge g_0(m)=m2^m.
\tag{17}
$$

The zero terms are equal to zero; Only "cut", "transient", and the E-limit branch are called with the same parameters for the smaller potential. Inherit this lower bound. E-successor Branch Iteration $x\mapsto f_{\rm PP}(\operatorname{cut}P,x)$ Total: $2^m$ times. The inductive lower bound for each recursive call is at least the current input. The first time has already been at least $g_0(m)$. Therefore, the entire iteration also satisfies (17). All the definitions used in the call originate from the same finite potential induction. No need to preset global monotonicity.

For the parameters that actually appear in this text, there is thus $G(m)\ge m2^m>m$. Therefore, (2) indeed strictly enhances the original pIBLP interface $q(5)>2^{G(1)}$, and (3) can perform self-feedback that is determined by the BMS computation.

However, (17) has only elementary growth universal bounds, and there is no establishment of $G$ to dominate the BMS with $D$, $T$, or $F_\Lambda$. Therefore, this paper does not complete the comparison between the pIBLP numerical interface and the optimal explicit BMS–FGH bounds. The addition of parent packages, the comparison of the order types of markings, and two inequalities that are both below $q(5)$, cannot replace the numerical dominance that still needs to be proven.

This paper is a paper-based construction. It does not calculate the decimal value of $G(1)$, does not run giant fixed-point descent, and does not modify the pIBLP generator.
