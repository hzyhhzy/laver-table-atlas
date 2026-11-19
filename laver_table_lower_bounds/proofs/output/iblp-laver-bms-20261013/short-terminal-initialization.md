# Implementation of the low endpoint of three-row BMS seeds · [中文版](short-terminal-initialization.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Under the assumption of I3, the order parameter of the first occurrence of a period in the first row of the ordinary Laver table satisfies 32

$$
q(5)>D_2(R_3),\qquad R_3=(000)(111)(111).
\tag{1}
$$

Here, the parentheses represent the columns of the BMS; $D_2$ represents the parent table that indicates the number of times $[2]$ is repeated to empty, that is, the number of times the original BM4 is repeated to $[1]$. $q(N)$ follows the same conventions as the BMS subscripts, as outlined in the general overview (historical reference: `README.zh-CN.md`).

The formula (1) consists of a finite initialization in this article and [Implementation-preserving properties and column deletion counts](<ribbon-initialization.md>). The lower bound is not inferred using a finite descent test. It has not yet reached the BMS[10] target for the eleventh row, nor has it converted $D_2$ into the specified FGH values.

## Seeds that repeat in a column and weaker initialization conditions

Let's denote the mathematical research manuscript as follows:

$$
B_h=(0^h)(1^h),\quad S_h=(0^h)(1^h)(2^h),\quad
P_h=(0^h)(1^h)(2,0^{h-1}),\quad R_h=(0^h)(1^h)(1^h).
$$

In the parent table, there are $P_h=((),0^h,(1))$, $R_h=((),0^h,0^h)$. Expressed directly.

$$
P_h[2]=R_h,\qquad D_2(P_h)=1+D_2(R_h).
\tag{2}
$$

These are standard descendants, not any non-standard matrices. From $S_h$, doing $h(h+1)/2-1$ times new $[1]$ gives $P_h$: when the last parent column is $1^a$, one step becomes $1^{a-1}0^{h-a+1}$, and doing another $h-a+1$ step results in $1^{a-1}$. Summing over $a=h,\ldots,2$ gives the above number of steps. The new $[1]$ is a prefix of the original positive expansion, thus maintaining standardness.

$$
B_h<R_h<P_h\le S_h<B_{h+1}.
\tag{3}
$$

The entire $R_h$ family converges to a BMS limit. The formula (3) represents only a ordinal relationship and does not imply a certain magnitude of the given FGH value.

Use the notation [Compatible mapping group](<ribbon-initialization.md>):

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1},
$$

$$
\operatorname{crit}(K_k)=U_0,\quad
K_k(U_i)=V_i\ (0\le i\le k),\quad K_k(V_0)=V_{k+1}.
\tag{4}
$$

Just find another embedding $L$ that satisfies

$$
\operatorname{crit}(L)=V_0,\qquad L(V_0)=V_{h+1}.
\tag{5}
$$

then $R_h$ Only ends are present. $L(V_{h+1})$ Implementation of the band.

Prove that taking three columns as $U_i$, $V_i$, $L(V_i)$, where $0\le i\le h$, the total end is $L(V_{h+1})$. The first positive column is realized by $K_k$; the second positive column is realized by $L(K_k)$. Since $L$ fixes all $U_i$, the identity is applied to give

$$
L(K_k)(U_i)=L(V_i),\qquad
L(K_k)(L(V_0))=L(V_{k+1}).
$$

Both columns have zero parents, and they exactly achieve $R_h$. The source column does not require positive port witnessing. Proof completed.

Compared to using the third critical image of the highest $K_h$ as the endpoint, 5) allows for independent selection of $L$, making it a weaker initialization condition. If $h\ge3$

$$
L(V_{h+1})\le j(\gamma_{N-1}),
$$

The column deletion count is immediately given as $D_2(R_h)<q(N)$.

## The literature points used are as follows:

Fix the I3 embedding in the $j$, and all the following terms are in the same $\operatorname{Iter}(j)$. Apply the writing $a(b)$, which cannot be read as a function composition. Let the $K=j_{(11)}$, and take

$$
(\theta_0,\ldots,\theta_8)=
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,
j_{(7)}(\kappa_2),j_{(11)}(\kappa_3),j_{(10)}(\kappa_3),
j_{(11)}(j_{(11)}(\kappa_3)),j_{(9)}(\kappa_3)).
$$

The required literature facts are:

$$
\theta_0<\cdots<\theta_8<\kappa_4,\quad
K(\theta_i)=\theta_{i+2}\quad(0\le i\le5),
\tag{6}
$$

and

$$
\theta_2<\gamma_3<\theta_3=\gamma_4,\qquad
\operatorname{crit}(j_{(8)})=\gamma_3,\quad
j_{(8)}(\gamma_3)=\theta_3,\quad j_{(8)}(\theta_3)=\theta_4.
\tag{7}
$$

(6) see [Qi, the 5th section](https://arxiv.org/html/2501.06733v5#S5); (7) see [Dougherty's first paper, section 5, presents 2](https://arxiv.org/pdf/math/9205202). Also, $j(\theta_i)=\theta_{i+1}$ holds for $0\le i\le2$, and $j(\theta_3)=\kappa_4$.

The following equations are based solely on these inputs, the fixity below the critical point, and

$$
a(b)(a(x))=a(b(x)),\qquad
\operatorname{crit}(a(b))=a(\operatorname{crit}(b))
\tag{8}
$$

Derivation.

## Explicit two-layer group

Define in sequence

$$
a=K(K),\ b=K(j),\ c=a(b),\ d=c(K),\ e=d(j),\
f=e(K),\ g=f(K),\ r=g(f),\ p=f(b),\ s=r(d),\
J=p(f),\ L_2=s(g).
\tag{9}
$$

Starting from (8)

$$
\begin{aligned}
a &: (\theta_2,\theta_3,\theta_4,\theta_5)
       \mapsto(\theta_4,\theta_5,\theta_6,\theta_7),\\
b &: (\theta_2,\theta_3,\theta_4)\mapsto(\theta_3,\theta_4,\theta_5),\\
c &: (\theta_4,\theta_5,\theta_6)\mapsto(\theta_5,\theta_6,\theta_7),\\
d &: (\theta_0,\theta_1,\theta_2,\theta_3)
       \mapsto(\theta_2,\theta_3,\theta_5,\theta_6),\\
e &: (\theta_2,\theta_3,\theta_5)\mapsto(\theta_3,\theta_5,\theta_6).
\end{aligned}
$$

Definition point

$$
\alpha=e(\theta_4),\quad\beta=f(\theta_2),\quad
\zeta=f(\theta_4),\quad\eta=r(\theta_3),\quad\rho=r(\theta_5).
$$

Successively obtained by strict monotonicity

$$
\theta_5<\beta<\alpha<\zeta<\eta<\rho<\theta_6.
\tag{10}
$$

The required point image is

$$
\begin{aligned}
f &: (\theta_0,\theta_1,\theta_3,\theta_5)
        \mapsto(\theta_3,\theta_5,\alpha,\theta_6),\\
g &: (\theta_3,\theta_5,\beta,\alpha)
        \mapsto(\beta,\alpha,\zeta,\theta_6),\\
r &: (\theta_0,\theta_1,\theta_2,\beta)
        \mapsto(\beta,\alpha,\zeta,\theta_6),\\
p &: (\beta,\alpha,\zeta)\mapsto(\alpha,\zeta,\theta_6),\\
s &: (\beta,\alpha,\zeta)\mapsto(\zeta,\eta,\rho),\\
J &: (\theta_0,\theta_1,\theta_2,\theta_3,\theta_4)
        \mapsto(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\end{aligned}
\tag{11}
$$

Enter the equations in one line without sorting them by size. For example, the line with $g$ only lists four corresponding equations.

The critical points of $f,J$ are all $\theta_0$.

$$
\operatorname{crit}(L_2)=\theta_3,\qquad
L_2(\theta_3)=\zeta,\qquad L_2(\zeta)=\rho.
$$

Therefore

$$
U=(\theta_0,\theta_1,\theta_2),\quad
V=(\theta_3,\theta_5,\alpha,\zeta),\quad
(K_1,K_2)=(f,J)
$$

Satisfying (4), and having a $L_2$ that satisfies (5).

## The third layer and independent end witnesses

Put

$$
\delta=J(\gamma_3),\quad H=J(j_{(8)}),\quad J_3=H(J).
$$

From (7) and (11),

$$
\alpha<\delta<\zeta,\quad
\operatorname{crit}(H)=\delta,\quad H(\delta)=\zeta,\quad H(\zeta)=\theta_6.
$$

Therefore, $H$ fixes $\theta_0,\theta_1,\theta_2,\gamma_3,\theta_3,\theta_5,\alpha$, thus

$$
J_3:(\theta_0,\theta_1,\theta_2,\gamma_3,\theta_3)
       \mapsto(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\tag{12}
$$

Let it be

$$
A=c(d),\qquad L_3=A(j(j)).
$$

As mentioned earlier $c,d$ Point-likeness and fixity

$$
A:(\theta_1,\theta_2,\theta_3)\mapsto(\theta_3,\theta_6,\theta_7).
$$

Since the critical sequence of $j(j)$ starts with $\theta_1\mapsto\theta_2\mapsto\theta_3$, therefore

$$
\operatorname{crit}(L_3)=\theta_3,\quad
L_3(\theta_3)=\theta_6,\quad L_3(\theta_6)=\theta_7.
\tag{13}
$$

Thus, a complete three-layer initialization is obtained.

$$
U=(\gamma_0,\gamma_1,\gamma_2,\gamma_3),\quad
V=(\theta_3,\theta_5,\alpha,\zeta,\theta_6),\quad
(K_1,K_2,K_3)=(f,J,J_3),\quad L=L_3.
$$

The end is $\theta_7<\kappa_4=j(\gamma_4)$. Substituting $h=3,N=5$ into the initialization lemma gives (1).

The independent algebraic verification program (historical reference: `three_row_certificate.py`) only loads the basic point images of (6)–(7) and $j$, and then verifies the derived application items of 17 and all compatible relationships. The program does not import the M historical search; it verifies finite algebraic derivations, not Lean formalizations, and does not re-prove the literature inputs.

## Extend the source interval while retaining the periodic endpoints

The source point has exhausted the four critical points marked with $\gamma_4$. Therefore, it is not possible to continue adding points to the tail of the source sequence with $V_0=\gamma_4$. The restriction on this position can be eliminated, but no additional eight layers of evidence have been provided yet.

Put

$$
T=j_{(9)}(j_{(15)}),\qquad Q=j_{(9)}(j_{(14)}).
$$

[Dougherty, Chapter 5](https://arxiv.org/pdf/math/9205202) Proof

$$
Q(T(T(\theta_6)))<\kappa_4.
\tag{14}
$$

Table 2 and the application identity are also provided.
$\operatorname{crit}(T)=\gamma_1$, $T(\gamma_1)=\theta_8$.
Due to

$$
\theta_7<\theta_8=T(\gamma_1)<T(\theta_6),
$$

There are

$$
T(\theta_7)<T(T(\theta_6))\le Q(T(T(\theta_6)))<\kappa_4.
\tag{15}
$$

The system of embeddings unified through the transport operation with $T$ still consists of a three-layer group whose end is lower than $\kappa_4$.

Now let $B=T(j_{(7)})$. It is given that 2 yields $j_{(7)}(\gamma_0)=\gamma_3$, $j_{(7)}(\gamma_1)=\gamma_4$, therefore

$$
B(\gamma_0)=T(\gamma_3),\qquad B(\theta_8)=T(\gamma_4).
$$

Also, due to $\gamma_8<\theta_8$, strict monotonicity provides eight clear candidates for the source point.

$$
T(\gamma_3)<B(\gamma_1)<\cdots<B(\gamma_8)<T(\gamma_4).
\tag{16}
$$

All of these points belong to the same set of critical points of $\operatorname{Iter}(j)$. They only address the problem of the positions of the sources; additional row embeddings that are compatible with each other and end-witnesses that preserve boundaries still need to be constructed. Therefore, it cannot be claimed that eleven layers of initialization have been achieved.

## Ascending condition with independent terminal witnesses

The independent witnesses of (5) can be transported along with the ascending layers. Assuming there are groups with a height of $h$ and $L$, let it be denoted as

$$
J=K_h,\quad S=V_{h+1}=J(V_0),\quad C=L(S).
$$

Select $U_h<u<V_0$ and let it be $\beta=J(u)$. If the embedding $H$ satisfies

$$
\operatorname{crit}(H)=\beta,\qquad H(\beta)=S,
\tag{17}
$$

So, use $H(J)$ as the new highest row embedding. Add the source point $u$ and the target point $H(S)$, and change the end witness to $L'=H(L)$.

Because $\beta>V_h\ge V_0$, $H$ fix the old source points and $V_0,\ldots,V_h$. Equation (8) provides all the new compatible relations, while

$$
\operatorname{crit}(L')=V_0,\quad
L'(V_0)=H(S),\quad L'(H(S))=H(C).
\tag{18}
$$

Therefore, by controlling just $H(C)\le\Theta$, one can complete a boundary-preserving upward leveling. Here, $C$ is the second critical image of the independent witness, and it is no longer forced to be equal to $J^{\circ3}(U_0)$.

For the eight points of (16), the specific conditions required are (17)–(18). Not all of these conditions have been established yet. Even if the eleventh layer is obtained, it is still necessary to prove that the corresponding decrease length exceeds the specified $F^{\rm BMS}_{B_{11}}(10)$. A larger seed ordinal cannot replace this numerical comparison.
