# A high common root chain that is still below the q(5) endpoint · [中文版](small-period-endpoint-Sf.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper proves a finite embedding algebra lemma and integrates it into the existing recursive corridor. It addresses specific endpoint resource issues. **No primary goal has been announced as having "substantial internal structure exceeding BMS" completed.**, has also not proven the original hypotheses about $K(\theta_6)<j(\gamma_5)$ or $K(\theta_6)<j(\gamma_6)$.

The key is to replace the transporter: use $A=S(f)$ instead of $K(K)(f)$. The entire text is fixed under ZFC + I3, with $j:V_\lambda\to V_\lambda$ fixed in place. All owners belong to the fixed $\operatorname{Iter}(j)$. The parentheses $u(v)$ indicate application; ordinary compositions are written as $u\circ v$.

<a id="proof-section-1"></a>

## The facts available for use in 1. and their sources

Continue to use

$$
K=j_{(11)},\qquad \mu=\theta_4,\qquad
\nu=j_{(9)}(\gamma_3),\qquad \theta_8=j_{(9)}(\kappa_3).
$$

Here, $\theta_i=\kappa_i$ holds for $0\le i\le3$; $\kappa_2<\gamma_3<\kappa_3$. The required strict order is

$$
\kappa_3<\mu<\theta_5<\theta_6<\theta_7<\nu<\theta_8<\kappa_4.
\tag{1}
$$

$K(\theta_i)=\theta_{i+2}\;(0\le i\le5)$, 
$j_{(9)}(\kappa_2)=\mu$, 
$j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3$, a finite point image computation from [Dougherty I, Section 5](https://arxiv.org/pdf/math/9205202). The same organization for $\theta_i$ is also described in [Qi, the 5 section](https://arxiv.org/html/2501.06733v5#S5). The strict comparison of $\theta_7<\nu$ with double truncation derivations is fully written out in [Endpoint Transport Manuscript](<promoted-bms-feedback.md#proof-section-2>), and is not guessed from $\theta_7<\theta_8$.

To clarify the origin of $f$, define the actual term

$$
a_*=K(K),\quad b_*=K(j),\quad c_*=a_*(b_*),\quad
d_*=c_*(K),\quad e_*=d_*(j),\quad f=e_*(K).
\tag{2}
$$

Using only the application identity $u(v)(u\xi)=u(v\xi)$ and fixity, we can obtain

$$
\begin{aligned}
a_* &: \theta_2\mapsto\theta_4,\quad
       \theta_3\mapsto\theta_5,\quad
       \theta_4\mapsto\theta_6,\quad
       \theta_5\mapsto\theta_7,\\
b_* &: \theta_2\mapsto\theta_3\mapsto\theta_4\mapsto\theta_5,\\
c_* &: \theta_4\mapsto\theta_5\mapsto\theta_6\mapsto\theta_7,\\
d_* &: \theta_0\mapsto\theta_2,\quad
       \theta_1\mapsto\theta_3,\quad
       \theta_2\mapsto\theta_5,\quad
       \theta_3\mapsto\theta_6,\\
e_* &: \theta_2\mapsto\theta_3\mapsto\theta_5\mapsto\theta_6.
\end{aligned}
\tag{3}
$$

For example, $d_*(\theta_3)=c_*(K(\theta_3))=c_*(\theta_5)=\theta_6$, because $c_*$ fixes $\theta_3<\operatorname{crit}(c_*)=\theta_4$. The critical point of $e_*$ is $\theta_2$, so it fixes $\theta_0,\theta_1$. Therefore,

$$
\boxed{f(\kappa_0)=\kappa_3,\qquad
f(\kappa_1)=\theta_5,\qquad f(\theta_5)=\theta_6.}
\tag{4}
$$

The last formula particularly requires to be written as $\theta_5=e_*(\theta_3)$:

$$
f(\theta_5)=e_*(K)(e_*(\theta_3))
=e_*(K(\theta_3))=e_*(\theta_5)=\theta_6.
$$

Put

$$
S=j_{(9)}(j_{(4)}).
$$

The above real point image is provided.

$$
\operatorname{crit}(S)=\mu,\qquad S(\mu)=\nu,\qquad S(\nu)=\theta_8.
\tag{5}
$$

Therefore, $S$ fixes $\kappa_0,\kappa_1,\kappa_2,\kappa_3$, and

$$
\theta_7<\nu<S(\theta_5)<S(\theta_6)<S(\theta_7)<\theta_8<\kappa_4.
\tag{6}
$$

The lower bound of the first image comes from $\mu<\theta_5$, and the upper bound of the last image comes from $\theta_7<\nu$. Additionally, $\theta_5<S(\theta_5)$ is not needed because $S(\theta_5)>\nu>\theta_5$ already exists; there is no need to additionally invoke the statement "all critical points will be moved."

## 2. Short Transport Lemma

Take

$$
A=S(f),\qquad Z=A(\theta_5),\qquad u_0=S(\theta_5).
\tag{7}
$$

Because $S$ fixes $\kappa_0,\kappa_1,\kappa_3$, it follows from (4)

$$
A(\kappa_0)=\kappa_3,\qquad A(\kappa_1)=u_0.
\tag{8}
$$

Also, due to strict monotonicity and $\theta_5<S(\theta_5)$,

$$
\boxed{Z=A(\theta_5)<A(S(\theta_5))
=S(f(\theta_5))=S(\theta_6)<\kappa_4.}
\tag{9}
$$

Here, the $A(\theta_5)$ is not mistakenly written as $S(f(\theta_5))$: the two are strictly less than relationships. In addition, the $\kappa_1<\theta_5$ is given as

$$
u_0=A(\kappa_1)<A(\theta_5)=Z.
\tag{10}
$$

Therefore, for **For any actual $M$-lined chain $(\kappa_0;\kappa_1,\ldots,\theta_5)$**, taking the $A$-image point by point and owner by owner, we obtain the actual $M$-lined chain.

$$
\boxed{(\kappa_3;S(\theta_5),\ldots,Z),\qquad
\theta_7<S(\theta_5)<Z<S(\theta_6)<\theta_8<\kappa_4.}
\tag{11}
$$

This quantifier refers to transporting a finite chain that already exists, without assuming any length of the original chain.

There is also a more general window conclusion:

$$
x<u_0=S(\theta_5)\quad\Longrightarrow\quad A(x)<S(a).
\tag{11a}
$$

This is because $A(u_0)=S(a)$. The input upper bound here is $u_0$, not just $\theta_5$.

## 3. Published large chain inputs

Use $C_{\rm line}$ to denote the actual length of the large chain called before this:

$$
(\kappa_0;\kappa_1,\ldots,\theta_5)
\quad\text{is }C_{\rm line}\text{-lined}.
\tag{12}
$$

It is a finite actual embedding witness given by [Proposition 1.3(1), Theorem 2.25, and Lemma 3.3 of Qi](https://arxiv.org/html/2501.06733v5). This paper follows the convention of using $2^{C_{\rm line}}=m_{\omega+2}(2)$ for constants. The proof shows that (11) does not depend on how this constant is estimated. In particular, the statement "there are many critical points below $\theta_5$" cannot be used to replace the lined property of (12).

Substitute (12) for (11), the common root is ($\kappa_3$, and the original feedback template uses

$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7.
$$

Therefore

$$
k<\kappa_3<a<c<u_0.
\tag{13}
$$

This exactly closes [Recursive corridor's high common root condition](<small-period-recursive-corridor.md#proof-section-2>), and there is no need to transition to $q(6)$ or $q(7)$.

## The precise conclusion of the recursive template with 4. access

Let $D(h)$ Just the original. BM4 for $(0^h)(1^h)(1^h)$ Repeat the operation $[1]$ Total number of times reaching empty.  $T(h)=D(h)+2$， And defined recursively

$$
F_0=T,\qquad
F_{i+1}(h)=F_i^{\circ(D(F_i(h))+1)}(h).
\tag{14}
$$

Let the owners of each segment of (11) be
$H_i:\kappa_3\mapsto u_i\mapsto u_{i+1}$，
$0\le i<C_{\rm line}$. Because $\kappa_2<\kappa_3<\theta_6$ and $c<u_i$.

$$
H_i\text{ fixes }\kappa_0,\kappa_1,k,\qquad
H_i(a)>u_i,\qquad H_i(c)<u_{i+1}.
\tag{15}
$$

By applying the existing recursive template lemma, it can be concluded that every $F_i$ has a natural implementation as an entrance $b$, and the $i+1$th exit can be taken as $H_i(c)<u_{i+1}$. Therefore, for fans with existing entrances and closures below $b$, heights of $h\ge3$ are obtained, resulting in heights of $F_{C_{\rm line}}(h)$ and entrances and closures below $Z<\kappa_4=j(\gamma_4)$. Counted and given

$$
q(5)>D(F_{C_{\rm line}}(h)).
\tag{16}
$$

It can also be **Clarify and upgrade once more**. The previous exit is lower than $Z<S(a)$, and $S$ fixes $\kappa_0,\kappa_1,k$ and $S(c)<\kappa_4$. Therefore, using the same lemma once more with $H=S$, we obtain

$$
\boxed{q(5)>D(F_{C_{\rm line}+1}(h)).}
\tag{17}
$$

This still only applies to the $h$ declarations supported by existing entrance fans; it does not assume that any natural number height can be initialized under the same entrance.

### The length of the 4.1 chain can also be generated from the calculations of existing fans.

Given (11a), the chain length does not have to be locked to $C_{\rm line}$. If there already exists a fan with a high $y$ and a sealed $C<u_0$, let

$$
N=D(y),\qquad m=\lfloor\log_2N\rfloor.
$$

The global count gives $\gamma_{2^m}\le\gamma_N<C<u_0$. Dougherty's actual $m$-lined chain $(\gamma_0;\gamma_1,\ldots,\gamma_{2^m})$, after taking the $A$-image, results in

$$
(\kappa_3;u_0,\ldots,A(\gamma_{2^m})),\qquad
A(\gamma_{2^m})<A(C)<S(a).
\tag{18}
$$

There are no additional reducibility chains, so the length is $m$, and it cannot be written directly as $N$.

For example, starting from an entrance fan with a height of $h$, perform a $T$ operation once to obtain a fan with a height of $T(h)$, and a fan with a seal lower than $c<u_0$. Take

$$
m(h)=\lfloor\log_2 D(T(h))\rfloor.
$$

Using the (18) support of the (14) $m(h)$ layer template, and then upgrading with the ($S$ once more, we can obtain

$$
\boxed{q(5)>D(F_{m(h)+1}(h)).}
\tag{19}
$$

The fan used to generate the chain and the initial fan used to execute the new template can be retained as two finite witnesses; there is no need to reverse the $T$ once, nor does it make the chain length dependent on the final output.

The order of quantifiers is as follows: First, construct the existing finite $T(h)$ and count their $D$, resulting in finite $m(h)$. Then, construct the finite chain of (18); subsequently, perform $m(h)+1$ finite inductions on the natural template; finally, apply the obtained template to the original input fan. No fixed endpoint is provided for any length of infinite witnesses. When transporting the entire finite background, (11a) becomes
$x<Q(u_0)\Rightarrow Q(A)(x)<Q(S(a))$，
Therefore, this parameterization process also maintains the necessary integrity and naturalness of the background.

## 5. Conclusion Boundary

What has been completed is a**A rigorous endpoint proof for the actual large chain within the $q(5)$ window**, as well as its integration into a finite induction with an existing natural template. Each segment of the11) can be used for the construction of subsequent internal structures. This paper does not equate the variable depth recursion of the $D$ black box with some established hyper-BMS ordinal notation; nor does it smuggle a chain of arbitrary length within a fixed window from the finite $C_{\rm line}$; nor does it claim that the old candidate upper bounds of the $K(\theta_6)$ have been proven or disproven.

The finite interface verification is shown as small_period_sf_endpoint_certificate.py (historical reference: `small_period_sf_endpoint_certificate.py`). It only verifies the point images of (7)—(11) and the strict order, does not run $D$, and does not materialize the edges of $C_{\rm line}$.
