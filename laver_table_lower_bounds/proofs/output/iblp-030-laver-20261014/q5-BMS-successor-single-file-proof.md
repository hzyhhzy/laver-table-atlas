# Laver's BMS limit successor layer lower bound of 32 periods · [中文版](q5-BMS-successor-single-file-proof.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Single-file paper proof. The axioms are assumed to be **ZFC + I3**, and have not yet been formalized in Lean.

Let $\Lambda=\lim(\mathrm{BMS})$. According to the fundamental sequences and fast-growing function conventions specified in this document, prove

$$
\boxed{\displaystyle
q(5)>F_{\Lambda+1}\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).
}\tag{Main theorem}
$$

Here, $q(5)$ is the first row cycle of the ordinary binary Laver table that first reaches $32$ at **Order parameter**: The table has $2^{q(5)}$ elements. The comparison is between two natural numbers, not between natural numbers and ordinals. $\Lambda+1$ represents a rapidly growing function in the next layer in the conclusion; this theorem does not claim that a new notation with a significantly stronger internal structure than BMS has been constructed.

The proof is divided into two parts. The first part transforms the Laver critical point intervals into iterable BMS computational budgets; the second part reduces the number of fixed index decrements to FGH, and pays for the number of rows and input costs item by item. All the new lemmas required for this study are proven in this paper; only the theorems listed in the 2 section are used as external inputs, without requiring readers to open other local research documents separately.

## The notation and counting conventions for 1 are as follows:

### 1.1 Ordinary Laver Table

$A_m$ is a common binary Laver table of size $2^m$, numbered $1,\ldots,2^m$, which satisfies the left distributive law and $a*1=a+1\pmod {2^m}$. The minimal period of the first row is denoted as $p_m$. Definition:

$$
q(n)=\min\{m:p_m\ge2^n\}.
$$

The following I3 exist as minimum values. Only $q(5)$ will be used in the following text.

Fix a I3 that embeds into $j:V_\lambda\to V_\lambda$. All witnesses belong to the same $\mathcal I=\operatorname{Iter}(j)$, allowing application and ordinary composition. $a(b)$ represents application; $a\circ b$ represents ordinary function composition, which should not be confused. Denote as

$$
j_{(1)}=j,\quad j_{(n+1)}=j_{(n)}(j),\quad
\kappa_0=\operatorname{crit}(j),\quad\kappa_{i+1}=j(\kappa_i),
$$

Enumerate all the critical points of $\mathcal I$ using $\gamma_0<\gamma_1<\cdots$. Each ordinal point named below belongs to this set.

### The indicators of the BMS with 1.2

The entire text is $M[n]$: **Original BM4 indicator**. In $[0]$, the last column is deleted. For the last column, the $[n]$ retains the prefix obtained from the deleted last column, and an additional $n$ copies of bad blocks are added. All zero-term columns are deleted in all indices. Therefore, the fixed value of $[1]$ in this document is equal to the fixed value of $[2]$ shown in the previous parent table version.

Let $Z$ be the all-zero sequence, and the parentheses indicate a matrix sequence. Define

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),
$$

$$
d_n(M)=\text{repeatedly applying }[n]\text{ steps to the empty matrix},\qquad
s_M(n)=\text{of these steps delete a zero last column},
$$

$$
D(h)=d_1(R_h),\qquad T(h)=D(h)+2.
$$

The self-loop of zero is not considered as a single step. The termination of all actual counting is guaranteed in the section 10. $T^{\circ a}$ always denotes a function composition of $a$ steps.

### 1.3 FGH is a convention

For the standard BMS formula, take

$$
F_\varnothing(x)=x+1,\qquad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\qquad
F_M(x)=F_{M[x]}(x)\quad(M\text{ has a nonzero last column}).\tag{1.1}
$$

The topmost element and its successors

$$
\Lambda[x]=B_{x+1},\qquad F_\Lambda(x)=F_{B_{x+1}}(x),\qquad
F_{\Lambda+1}(x)=F_\Lambda^{\circ(x+1)}(x).\tag{1.2}
$$

The finite subscript $n$ refers to $Z^n$. In particular

$$
F_1(x)=2x+1,\qquad F_2(x)=(x+1)2^{x+1}-1,\qquad
t:=F_3(256)=F_2^{\circ257}(256).\tag{1.3}
$$

## 2 explicitly refers to cited literature inputs.

The following is a mathematical research paper, not a theorem or basic calculation tested by finite procedures to verify the properties of the assumptions.

The order type of the set of critical points for **Laver–Dougherty correspondence.** $\mathcal I$ is $\omega$.
$\kappa_0=\gamma_0,\kappa_1=\gamma_1,\kappa_2=\gamma_2,\kappa_3=\gamma_4$.
If $j(\gamma_n)=\gamma_a$, the first period does not exceed $2^n$ at the table order $a$, and it first exceeds $2^n$ at the table order $a+1$. The period either remains the same or doubles. Therefore

$$
\kappa_4=\gamma_s\quad\Longrightarrow\quad q(5)=s+1.\tag{2.1}
$$

In the same algebra, for each $m\ge1$, there exists a $m$-lined $(\gamma_0,\gamma_1,\gamma_{2^m})$ that serves as a witness; each segment can be taken as $j_{(2^{2^i}-1)}$, $0\le i<m$. The source is [Dougherty, Article 2, Section 2, and Theorem 3.1(c)](https://arxiv.org/pdf/math/9503204). The definition of lined is found in section 3.

Set **Finite point images and truncation.** as $K=j_{(11)}$, and also

$$
(\theta_0,\ldots,\theta_8)=
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,
j_{(7)}(\kappa_2),K(\kappa_3),j_{(10)}(\kappa_3),K(K(\kappa_3)),j_{(9)}(\kappa_3)).
$$

Using the following limited information; denote $\mu=\theta_4$:

$$
\begin{gathered}
\theta_0<\cdots<\theta_8<\kappa_4,\qquad
K(\theta_i)=\theta_{i+2}\quad(0\le i\le5),\\
\operatorname{crit}(j_{(10)})=\kappa_1,\quad
j_{(10)}(\kappa_1)=\kappa_2,\quad j_{(10)}(\kappa_2)=\mu,\\
j_{(3)}:\kappa_0\mapsto\kappa_2\mapsto\kappa_3,
\quad j_{(3)}(\kappa_1)=\gamma_3,\quad\kappa_2<\gamma_3<\kappa_3,\\
j_{(4)}:\kappa_2\mapsto\gamma_3\mapsto\kappa_3,
\qquad j_{(9)}(\kappa_1)=\kappa_2,\\
K\equiv_\mu j\circ j,\qquad
j_{(3)}\equiv_{\gamma_3}j\circ j.
\end{gathered}\tag{2.2}
$$

The sources are [Dougherty, Chapter 5](https://arxiv.org/pdf/math/9205202) and [Qi, the 5th section](https://arxiv.org/html/2501.06733v5#S5). $\equiv_\delta$ is a membership truncation equivalence, not a function equality at any low input. It follows its standard rules.

$$
a(b)\equiv_{\operatorname{crit}(a)}b,\qquad
a\equiv_\delta b\Longrightarrow Q(a)\equiv_{Q(\delta)}Q(b).\tag{2.3}
$$

Truncation can reduce and transfer; only the **The output is strictly below the cut-off point.** on one side can read the corresponding point image equality. The basic identity for application is

$$
a(b)(a(\xi))=a(b(\xi)),\quad
\operatorname{crit}(a(b))=a(\operatorname{crit}(b)),\quad
a(b(c))=a(b)(a(c)),\quad
a(b\circ c)=a(b)\circ a(c).\tag{2.4}
$$

Each embedding is strictly increasing, and it fixes the ordinal number that is less than the critical point.

**The actual long chain of Qi.** has actual evidence of $C_{\rm line}$-lined $(\kappa_0,\kappa_1,\theta_5)$, where

$$
2^{C_{\rm line}}=m_{\omega+2}(2),\quad
m_0(n)=n^n,\quad m_{\alpha+1}(n)=m_\alpha^{\circ n}(n),\quad m_\omega(n)=m_n(n).
\tag{2.5}
$$

The chain constructed here is from [Proof and Lemma of the Proposition 1.3(1): 3.3](https://arxiv.org/html/2501.06733v5#S3), and it does not derive the existence of the chain from the lower bound of a critical point.

The standard BMS well-order with the standard **BMS Well-ordering and Parent Table Formulas.** is described in Section 9. The source is [《Well-Orderedness of the Bashicu Matrix System》](https://arxiv.org/html/2307.04606v2), where the parent table replication is shown in Lemma 2.5. This paper also proves the coverage and termination interface of non-standard auxiliary matrices.

This lists the external inputs. The argument assumes neither well-foundedness of the full IBLP nor an unproved comparison of IBLP 030 with a growth function. It does not require every matrix with more rows to dominate every matrix with fewer rows.

## Part One: Laver Endpoints and BMS Calculations

## The operations of the finite chain with 3

We call $(r;a,b)$ $m$-lined if there exist $a=u_0<\cdots<u_m=b$ and $Q_i\in\mathcal I$ satisfying

$$
\operatorname{crit}(Q_i)=r,\quad Q_i(r)=u_i,\quad Q_i(u_i)=u_{i+1}
\quad(0\le i<m).
\tag{3.1}
$$

Take any image of the points and witnesses, denoted by $H$. From (2.4), we obtain a chain of points with the same length, denoted by $(H(r);H(a),H(b))$.

**Abbreviation.** can be replaced by $U:r\mapsto x\mapsto y$ and $V:r\mapsto y\mapsto z$ with $V(V)(U):r\mapsto x\mapsto z$. Because the critical point of $V(V)$ is $y$, fix $r,x$, and send $y$ to $z$. Thus, any non-empty chain can be reduced to a smaller positive length, while retaining the three endpoints.

**Chain multiplication.** If $(r;a,b)$ is $m$-lined, $(a;b,c)$ is lined with $n$. Then $(r;a,c)$ is $m2^n$-lined.

Proof of induction for $n$. At $n=1$, Use Unique Witness $H:a\mapsto b\mapsto c$ to carry the first chain. Obtain the $m$ segment of $(r;b,c)$. Combined with the original chain to form the segment $2m$. In general cases, The second chain takes the first segment $n-1$ first. The segment from $a$ to the penultimate endpoint, $m2^{n-1}$, is derived through induction. Only the segments before $n-1$ in the first and second chains were used together to witness the final transfer. The remaining $m2^{n-1}$ segment from the second last endpoint to $c$ is summarized. Just splice them together. This also directly proves the special case of the Qi chain multiplication used in this paper.

## 4 closure compatible groups and weak bands implementation

### 4.1 Closed Compatible Group

A closed compatible set of points with a height $h$ is strictly increasing.

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1}<C
$$

And the embedding $K_1,\ldots,K_h,L\in\mathcal I$, which satisfies

$$
\operatorname{crit}(K_i)=U_0,\quad K_i(U_t)=V_t\ (0\le t\le i),\quad
K_i(V_0)=V_{i+1},
\tag{4.1}
$$

$$
\operatorname{crit}(L)=V_0,\quad L(V_0)=V_{h+1},\quad L(V_{h+1})=C.
\tag{4.2}
$$

$C$ is called a closure. The groups constructed in this paper all have $U_0=\kappa_0,U_1=\kappa_1$.

### The definition of weak band realization with 4.2

Fix the matrix height $h$, and set it as $w=h+1$. Select a $\alpha_0<\cdots<\alpha_{mw}$ for a $m$ column matrix. Use $\alpha_{jw},\ldots,\alpha_{jw+h}$ for the $j$ column, with the right endpoint being $\alpha_{(j+1)w}$. If there is a parent column $c$ in the $k-1$ row, where $1\le k\le h$, then the actual embedding $J_{j,k}$ is required to satisfy the conditions.

$$
\operatorname{crit}(J_{j,k})=\alpha_{cw},\quad
J_{j,k}(\alpha_{cw+t})=\alpha_{jw+t}\ (0\le t\le k),\quad
J_{j,k}(\alpha_{jw})=\alpha_{jw+k+1}.\tag{4.3}
$$

Zero ports, anchor ports $k=0$ do not require embedding witness. This is **Implementation of weak bands**, which is not a complete ordinary BLS; the maintainability is proven directly below, without relying on the existence of a complete BLS.

Group (4.1)–(4.2)) implements $R_h$: three with them placed in sequence
$U_0,\ldots,U_h$, $V_0,\ldots,V_h$, $L(V_0),\ldots,L(V_h)$，
The total closure is $C$. The first positive column is denoted by $K_k$, and the second positive column by $L(K_k)$. Since $L$ fixes all $U_t$, the parent of both columns is the zero-th column. All (4.3) are given by (2.4).

### 4.3 step-preserving and its endpoint cost

Assign each port with a number $b_j+k$, where $b_j=3+jw$. The form of the anchor points and zero ports is denoted as $(0,b_j+k,b_j+k+1):1$; the form of the positive ports is denoted as

$$
(b_c,\ldots,b_c+k,b_j,\ldots,b_j+k,b_j+k+1):(k+1).\tag{4.4}
$$

The notation $0,1,2$ is merely a grammatical safeguard and does not participate in the ordinal value assignment in weak implementations.

If the last column is all zeros, delete the last $w$ endpoints to achieve its expansion. If the highest positive port of the last column that is $x$ is $k$, and the parent is $c$, then delete the $h-k$ end points first. The active embedding $J=J_{x,k}$ will transport the points of the source interval.

$$
\alpha_{cw+k}<\alpha_t<\alpha_{xw}
$$

Send between the last two points $\alpha_{xw+k},\alpha_{xw+k+1}$. Insert these images in order; the images from the first $k$ ports have been specified by (4.3)), and the points before the source base point are fixed. Each replicated positive row is witnessed by $J(K)$, satisfying (2.4); the zero row does not require witnessing.

In the formal row, this exactly replicates the interval $[b_c+k,b_x)$. The address $<b_c$ remains fixed, and all addresses $\ge b_c$ are translated by $(x-c)w$. The old end with the previous $k$ ports is retained, along with copies of the remaining ports from the parent, forming a new start: the active row inherits the old end columns, while the active row and above inherit the parent columns. The remaining bands are replicated in the same manner, consistent with the BMS parent table formula in section 9. The replication results in exactly $2x-c$ columns, without leaving any half-end bands.

Therefore, the operation BM4 $[1]$ can be achieved by the $h-k$ number of column deletions and one time **Keep the seal on** replication. Each insertion point is a critical point within the same $\mathcal I$. This encoding does not require any completion: The formal line (4.4) completion scan first encounters an anchor point, and the reference to that anchor point is $0$, which immediately crosses the lower bound. This proof only uses the aforementioned explicit operations, thus there is no need to assume that the M preservation theorem of the complete BLP remains valid.

### The total number of steps with 4.4 is strictly less than the number of column deletions.

Let the initial number of descending columns with $[1]$ be fixed as $m>0$. The steps can be divided into four categories:

- $u$: Non-zero last column, active port $k=h$, bad block width $d=1$;
- $v$: Non-zero last columns, $d\ge2$;
- $s$: Non-zero last columns, $d=1,k<h$;
- $z$: Deleting the zero-th last column.

Let the total number of column deletions be $\delta$, and the total number of BMS steps be $D_*=u+v+s+z$. The number of columns is conserved, as well as the definition of operations.

$$
z=m+\sum_{\text{positive steps}}(d-1)\ge m+v,\qquad
\delta=\sum_{\text{positive steps}}(h-k)+(h+1)z\ge s+(h+1)z.\tag{4.5}
$$

Also, there is $u\le v+z$. The proof considers the positive steps of the continuous $d=1$, with the penultimate column $Q$ remaining unchanged. After one occurrence of $u$, if there is still a highest row in $Q$, the highest parent of the new last column's $Q$ becomes the next bad block's width, which must be at least 2. If there is no highest row in $Q$, the height of the new last column is reduced to $h-1$, and it cannot rise back to $h$ until $v$ or $z$ are encountered. Each $u$ is assigned to the first $v$ or $z$ following it, and no assignment will be repeated. Ultimately, the deletion of empty columns ensures the existence of this subsequent step.

Therefore

$$
D_*\le s+2v+2z\le s+4z-2m
\le\delta-(h-3)z-2m<\delta\quad(h\ge3).\tag{4.6}
$$

If the initial seal is $\gamma_a$, each deletion strictly reduces the global critical point index at the end, and replication does not increase the end, hence $\delta\le a$. In particular, a group seal with a height of $h\ge3$ results in a seal of $C=\gamma_a$.

$$
\boxed{D(h)<a,\qquad\gamma_{D(h)}<C.}\tag{4.7}
$$

If $C<\kappa_4$, then from (2.1), we obtain $q(5)>D(h)$. This step controls the order of the table, not just the number of elements in the table.

## All terms with finite initialization marked as 5

This section only uses (2.2)–(2.4)). To avoid confusion with the subsequent window endpoint $a,b,c$, the auxiliary term is suffixed:

$$
a_*=K(K),\ b_*=K(j),\ c_*=a_*(b_*),\ d_*=c_*(K),\ e_*=d_*(j),
$$

$$
f=e_*(K),\ g_*=f(K),\ r_*=g_*(f),\ p_*=f(b_*),\ s_*=r_*(d_*),\
J=p_*(f),\ L_2=s_*(g_*).\tag{5.1}
$$

The first batch of points is as follows. Each row corresponds one-to-one with the input and output order:

$$
\begin{array}{c|c|c}
\text{term}&\text{input}&\text{output}\\\hline
a_*&(\theta_2,\theta_3,\theta_4,\theta_5)&(\theta_4,\theta_5,\theta_6,\theta_7)\\
b_*&(\theta_2,\theta_3,\theta_4)&(\theta_3,\theta_4,\theta_5)\\
c_*&(\theta_4,\theta_5,\theta_6)&(\theta_5,\theta_6,\theta_7)\\
d_*&(\theta_0,\theta_1,\theta_2,\theta_3)&(\theta_2,\theta_3,\theta_5,\theta_6)\\
e_*&(\theta_2,\theta_3,\theta_5)&(\theta_3,\theta_5,\theta_6)
\end{array}\tag{5.2}
$$

For example, $c_*(\theta_4)=a_*(b_*)(a_*(\theta_2))=a_*(\theta_3)=\theta_5$.
$d_*(\theta_2)=c_*(K)(c_*(\theta_2))=c_*(\theta_4)=\theta_5$，
Because $\operatorname{crit}(c_*)=\theta_4$ fixes $\theta_2$. The remaining equations can also be directly substituted with (2.4).

Definition

$$
\alpha=e_*(\theta_4),\quad\beta=f(\theta_2),\quad
\zeta=f(\theta_4),\quad\eta=r_*(\theta_3),\quad\rho_0=r_*(\theta_5).
$$

From (5.2) and monotonicity, it follows that
$\theta_5<\alpha<\theta_6$, $\theta_5<\beta<\alpha$, 
$\alpha<\zeta<\theta_6$. Continue transporting.

$$
\begin{array}{c|c|c}
f&(\theta_0,\theta_1,\theta_3,\theta_5)&(\theta_3,\theta_5,\alpha,\theta_6)\\
g_*&(\theta_3,\theta_5,\beta,\alpha)&(\beta,\alpha,\zeta,\theta_6)\\
r_*&(\theta_0,\theta_1,\theta_2,\beta)&(\beta,\alpha,\zeta,\theta_6)\\
p_*&(\beta,\alpha,\zeta)&(\alpha,\zeta,\theta_6)\\
s_*&(\beta,\alpha,\zeta)&(\zeta,\eta,\rho_0)\\
J&(\theta_0,\theta_1,\theta_2,\theta_3,\theta_4)&(\theta_3,\theta_5,\alpha,\zeta,\theta_6).
\end{array}\tag{5.3}
$$

For example, $J(\theta_2)=p_*(f(\theta_2))=p_*(\beta)=\alpha$, because $p_*$ fixes $\theta_2$. Substituting $\theta_2<\theta_3<\theta_5<\beta$ into $r_*$ gives

$$
\theta_5<\beta<\alpha<\zeta<\eta<\rho_0<\theta_6.\tag{5.4}
$$

Critical points are calculated synchronously by (2.4)). The critical points of $f,J$ are $\theta_0$, $\operatorname{crit}(L_2)=\theta_3$, and there is also $L_2(\theta_3)=\zeta,L_2(\zeta)=\rho_0$. Therefore

$$
U=(\kappa_0,\kappa_1,\kappa_2),\quad
V=(\kappa_3,\theta_5,\alpha,\zeta),\quad(K_1,K_2)=(f,J),\quad L=L_2
\tag{5.5}
$$

It is a group that is highly 2 and sealed $\rho_0<\theta_6$.

Define the following mathematical research manuscripts:

$$
A_*=c_*(d_*),\qquad L_3=A_*(j(j)).
$$

From (5.2),$A_*$), send $(\theta_1,\theta_2,\theta_3)$ to $(\theta_3,\theta_6,\theta_7)$. The first three elements of the critical sequence of $j(j)$ are $\theta_1,\theta_2,\theta_3$, therefore

$$
L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7.\tag{5.6}
$$

It is not necessary to construct the third layer group first; (5.6) are independent actual application items.

## 6 generates high groups from any given long chain

The proof is as follows: By a universal lemma, if there exist $m$-lined $(\kappa_2;a_0,a_m)$, $a_0\ge\theta_6$, then there exists a group with a high degree $m+2$ and a cap below $a_m$. The witnesses of the input chain must belong to the ambient algebra $\mathcal I$.

### Insert a layer of local formulas into 6.1

There are groups with a high level of $h$ at the bottom, which are $\kappa_0,\kappa_1$. If there are $D_*$ and $\delta$ that satisfy

$$
\operatorname{crit}(D_*)=\kappa_0,\quad
D_*(\kappa_0)=V_0,\quad D_*(\kappa_1)=\delta,\quad D_*(V_0)=V_1,
$$

$$
V_0<\delta<V_1,\qquad K_i\equiv_\delta D_*\quad(1\le i\le h),\tag{6.1}
$$

Take any $T_*$ as the critical point $\kappa_1$, set $v=T_*(D_*)(\kappa_1)$, and define

$$
\begin{aligned}
U'&=(\kappa_0,\kappa_1,T_*(U_1),\ldots,T_*(U_h)),\\
V'&=(T_*(V_0),v,T_*(V_1),\ldots,T_*(V_{h+1})),\\
K'&=(T_*(D_*),T_*(K_1),\ldots,T_*(K_h)),\quad L'=T_*(L).
\end{aligned}\tag{6.2}
$$

There are

$$
T_*(V_0)<v<T_*(D_*)(T_*(\kappa_1))=T_*(\delta)<T_*(V_1).\tag{6.3}
$$

Therefore, all old owners' images at the new source $\kappa_1$ can be read from the truncated equivalent after handling; $v$. The other sides are directly obtained from (2.4)). The seal is $T_*(C)$. All owners of the new group are equal to the lowest owner below $T_*(\delta)>v$. This proves that local insertions and common truncation invariants exist.

### 6.2 provides low-bit truncation for a chain

Given $\operatorname{crit}(Q)=\kappa_2$, let $T_*=Q(j_{(10)}),Z_*=Q(j_{(3)})$. From (2.2),

$$
\operatorname{crit}(T_*)=\kappa_1,\quad T_*(\kappa_1)=Q(\kappa_2),
$$

$$
Q(K)=T_*(Q(j))\equiv_{T_*(\kappa_2)}T_*(j),\qquad
Q(K)\equiv_{Q(\gamma_3)}Z_*.
\tag{6.4}
$$

First, from monotonicity, we get $T_*(j)(\kappa_1)<T_*(\kappa_2)$, and then a valid readout yields $T_*(j)(\kappa_1)=Q(\kappa_3)$. Therefore

$$
Q(\gamma_3)<Q(\kappa_3)<T_*(\kappa_2),\qquad
T_*(j)\equiv_{Q(\gamma_3)}Q(j_{(3)}).\tag{6.5}
$$

if $Q_*$ The critical point is also... $\kappa_2$ ， Or an identity transport word. Then $Q_*(j)\equiv_{\kappa_2}j$. The same applies to $X=T_*(Q_*(j))$.

$X\equiv_{T_*(\kappa_2)}T_*(j)$. First, read the point image with $T_*(j)(\kappa_1)=Q(\kappa_3)<T_*(\kappa_2)$, then reduce the truncation to $Q(\gamma_3)$ to obtain

$$
X\equiv_{Q(\gamma_3)}Z_*,\qquad X(\kappa_1)=Q(\kappa_3).\tag{6.6}
$$

### A unified reconstruction of the next lowest possessor 6.3

For the general compound term $A=a_1\circ\cdots\circ a_t$, it is agreed that $A(b)$ represents the factor-by-factor application of transport. The rule is generalized by (2.4) for word lengths, still satisfying the same point image, LD, and truncation transport laws.

Inductive maintenance of the lowest possessor

$$
K_1=A(j_{(3)}),\quad A=P_*\circ T_*\circ Q_*,\tag{6.7}
$$

Among them, all factors of $P_*$ have critical points greater than $\kappa_1$, and the same applies to $T_*,Q,Q_*$. All owners are equal to $K_1$ below some $\varepsilon>V_1$. Let

$$
Y=P_*(X)=A(j),\quad Z'=P_*(Z_*),\quad
b'=P_*(Q(\kappa_2))=A(\kappa_1),\quad
\zeta'=P_*(Q(\gamma_3)),\quad W=A(j_{(2)}).
$$

Then

$$
\begin{gathered}
\operatorname{crit}(Y)=\operatorname{crit}(Z')=\kappa_0,\quad
Y(\kappa_0)=Z'(\kappa_0)=b',\\
Y(\kappa_1)=P_*(Q(\kappa_3)),\quad Z'(\kappa_1)=\zeta',\quad
Z'(b')=P_*(Q(\kappa_3)),\quad b'<\zeta'<Y(\kappa_1),\\
\operatorname{crit}(W)=b'>\kappa_1,\qquad W(b')=A(\kappa_2)=V_0.
\end{gathered}\tag{6.8}
$$

Set to $D_*=W(Z'),\delta=W(\zeta')$. $W$ Fixed to $\kappa_0,\kappa_1$. Therefore, $D_*$ satisfies four point similarities with 6.1). Among them

$$
D_*(V_0)=W(P_*(Q(\kappa_3)))=W(Y)(\kappa_1)=K_1(\kappa_1)=V_1.
$$

The transport (6.6) results in $K_1=W(Y)\equiv_\delta W(Z')$. There is also $V_0<\delta<V_1<\varepsilon$, so all owners satisfy (6.1).

Insert the following $T'=Q'(j_{(10)})$, and the new lowest possessor is

$$
T'(D_*)=A'(j_{(3)}),\quad
A'=P'\circ T'\circ Q,\quad P'=T'(W)\circ T'(P_*).\tag{6.9}
$$

The critical points of each factor $P'$ are still greater than those of $\kappa_1$, and the common truncation is maintained by (6.3)). Thus, the inductive invariants are closed.

### 6.4 Start point and closure

Starting from the group of (5.5) of height 2, take for the first time
$D_0=e_*(j_{(3)}),\delta_0=e_*(\gamma_3)$.
Given (2.2),$f=e_*(K)\equiv_{\delta_0}D_0$; $J=p_*(f)\equiv_{\operatorname{crit}(p_*)}f$, and)
$\delta_0<\theta_5<\operatorname{crit}(p_*)=\beta$.
Point images satisfy (6.1). After the first insertion, in (6.7), it is possible to take ($P_*=T_0(e_*),T_*=T_0,Q_*$ as the identity transport word, so it can be uniformly reconstructed thereafter.

Let the input chain be $Q_i:\kappa_2\mapsto a_i\mapsto a_{i+1}$, and take $T_i=Q_i(j_{(10)})$ in turn. If the current seal is $C_i<a_i$, then

$$
C_{i+1}=T_i(C_i)<T_i(a_i)=Q_i(\mu)<Q_i(a_i)=a_{i+1}.\tag{6.10}
$$

The final rigor is denoted by $\mu<\theta_6\le a_0\le a_i$. The initial state is $C_0=\rho_0<\theta_6\le a_0$. The induction is carried out for $m$ times, resulting in groups with a high degree of $m+2$ and groups with a lower closure than $a_m$. The full statement is proven by the insertion lemma.

## 7 feedback window and periodic transport

### 7.1 base window

Definition

$$
k=\kappa_2,\quad a=\theta_6,\quad b=L_3(\theta_5),\quad c=\theta_7,
\quad E=L_3(K),\quad P=L_3(f).
$$

From (5.3), (5.6), and (2.4),

$$
k<a<b<c<\kappa_4,\quad
E(\kappa_0)=k,\ E(\kappa_1)=a,\ E(a)=b,
$$

$$
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c.\tag{7.1}
$$

Let $W=L_3(b_*)$, $a'=L_3(\mu)$. Then $W:k\mapsto a\mapsto a'\mapsto b$, so $W,W(W)(W)$ gives a two-part chain of $(k;a,b)$.

The (2.5)) long chain is taken as the $E$-like, with a root of $k$, a starting point of $a$, and an end point of $E(\theta_5)<E(a)=b$. The 6 section provides the height.

$$
h_0=C_{\rm line}+2\tag{7.2}
$$

And the groups that are sealed below $b$. Taking the prefix of the chain, we also obtain such groups for each $3\le h\le h_0$.

### The strict endpoint bounds of the transporter 7.2

Let $\nu=j_{(9)}(\gamma_3)$. First, prove

$$
c=\theta_7<\nu<\theta_8<\kappa_4.\tag{7.3}
$$

The last two items are derived from (2.2) and monotonicity. Take

$$
V_*=j_{(10)}(j_{(10)}),\quad A=j_{(9)}(j_{(3)})=V_*(j_{(10)}),
\quad B=V_*(j),\quad Q=j_{(10)}(K)=V_*(K)=A(B).
$$

These identity terms are directly derived from the LD, not based on finite point image identifications and embeddings. $\operatorname{crit}(V_*)=\kappa_2$, therefore $B\equiv_{\kappa_2}j$. At the same time, $A(\kappa_1)=\mu,A(\kappa_2)=\nu$, so $Q\equiv_\nu A(j)$. Since $\kappa_3<\mu=A(\kappa_1)$, there is

$$
A(j)(\kappa_3)<A(j)(A(\kappa_1))=A(\kappa_2)=\nu.
$$

The legal reading is worth $Q(\kappa_3)<\nu$. On the other hand, transport $K\equiv_\mu j\circ j$, resulting in
$Q\equiv_{j_{(10)}(\mu)}K\circ K$.
From $j_{(9)}(\kappa_1)=\kappa_2$, we get $j_{(9)}(\kappa_2)=\mu$ and $j_{(10)}(\mu)=\theta_8$. Also, since $K(K(\kappa_3))=\theta_7<\theta_8$, then $Q(\kappa_3)=\theta_7$, proving (7.3).

Now let

$$
S=j_{(9)}(j_{(4)}).
$$

Given (2.2), $S:\mu\mapsto\nu\mapsto\theta_8$, fixed by $k$. Using $\mu<a<b<c<\nu$, we obtain

$$
\boxed{c<S(a)<S(b)<S(c)<\theta_8<\kappa_4.}\tag{7.4}
$$

### 7.3 Background Feedback Lemma

Let $H\in\mathcal I$ be fixed at $\gamma_0,\gamma_1$. It is not required to fix $k$ either. Then, any group with height $x\ge3$ and seal $C<H(b)$ can be transformed into a group with height $T(x)$ and seal $H(c)$.

First, let's explain why the universal insertion tool can perform transport. Take the **Background constants, terms, point images, and cut-off points** from the 5–6 section as a $H$-image, and use the same formula from the 6 section to perform finite induction on any newly introduced chain. The root of the new chain is $H(k)$, and the starting point is not lower than $H(a)$. Since $H$ fixes the first two source points, the bottom of the output group remains $\kappa_0,\kappa_1$. The strict guards of (6.1)–(6.10)) are all transported. These formulas only require the new chain to witness in the ambient algebra that **It is not required that a new witness is a $H$-image of some old witness.**. Therefore, it is not the case that there is no inverse image for any input, nor do we use the critical point numbers of $\operatorname{Iter}(H(j))$.

For the given input, set $N=D(x),m=\lfloor\log_2N\rfloor$. $N\ge3$, derived from (4.7))

$$
\gamma_{2^m}\le\gamma_N<C<H(b).\tag{7.5}
$$

Take the $m$ segment chain of the global Dougherty, multiply it by the $H(P)$-image, and then multiply it by the $H$-image segment chain, resulting in

$$
(H(k);H(a),Z)\text{ of }2^{m+1}\text{ segment chain},\qquad
Z=H(P)(\gamma_{2^m})<H(P)(C)<H(P)(H(b))=H(c).
$$

Due to $N<2^{m+1}$, the preservation of endpoints is reduced to the $N$ segment, and then the full-inclusion lemma is applied after transportation. The output height is $N+2=T(x)$, and the sealing is below $Z<H(c)$. The lemma is proven. The $H$ holds even when performing identity transportation, providing a one-time feedback for the basic window $b\to c$.

## The number of feedbacks for 8 is also determined by a single BMS calculation.

First, prove the chain feedback. Suppose there is a actual $M$ segment chain with $(k;u_0,\ldots,u_M)$, $c<u_0$, witnessing $Q_i:k\mapsto u_i\mapsto u_{i+1}$. Each $Q_i$ fixes $\gamma_0,\gamma_1$, and

$$
u_i=Q_i(k)<Q_i(b),\qquad Q_i(c)<Q_i(u_i)=u_{i+1}.\tag{8.1}
$$

Therefore, the groups with a closure lower than $u_i$, after the $Q_i$-background feedback in the 7.3 section, have a closure lower than $u_{i+1}$, and are applied with a height of $T$ once. After a finite number of $M$ iterations, the output height reaches $T^{\circ M}(x)$. Different chains and backgrounds are used in different rounds, and they are not unconditionally cycled within the same window.

Take any allowed $h$ from the 7.1 section. For basic feedback, first give the group with a height of $T(h)$ and a seal of $C_1<c$. Set

$$
N=D(T(h)),\qquad m=\lfloor\log_2N\rfloor.
$$

From (4.7),$\gamma_{2^m}\le\gamma_N<C_1<c<S(b)$. Take the global Dougherty chain as the $S(P)$-image, connect two segments of the $S$-image, and then preserve the endpoint shortening to obtain the $(k;S(a),Z)$ segment chain of the $N$ segment chain, where

$$
Z=S(P)(\gamma_{2^m})<S(P)(C_1)<S(P)(S(b))=S(c)<\kappa_4.\tag{8.2}
$$

The root remains $k$, as $S$ fixes it; the starting point is $S(a)>c>C_1$, so chain feedback can be executed. Starting from a group of height $T(h)$, execute $N$ rounds to obtain a group with a height of $T^{\circ(N+1)}(h)$ and a seal lower than $Z<\kappa_4$. Finally, use (4.7) and (2.1):

$$
\boxed{q(5)>D\!\left(T^{\circ(D(T(h))+1)}(h)\right)
\quad(3\le h\le C_{\rm line}+2).}\tag{8.3}
$$

First construct the first output group and determine the finite integer $D(T(h))$. Then construct a chain of that length and perform the same number of finite induction steps. This order of quantifiers defines the length independently of the final output and proves that the output exists.

## Part Two: Fixed Index Downward Movement and FGH

## 9 The parent table and auxiliary matrix domains of a regular BMS

Column numbers and row numbers start from 0. $P_q(i)$ represents the parent item in the $i$th column and the $q$th row; $p\prec_q i$ represents the parent chain along this row, and $p$ is a non-empty ancestor of $i$. The parentless coordinates are 0; parent coordinates that satisfy

$$
a_{i,q}=1+a_{P_q(i),q}.\tag{9.1}
$$

The specifications for the parent table domains require that the parent items point to the left, there are no empty spaces in the positive coordinates, the ancestors of higher rows are also ancestors of lower rows, and the numerical matrix recovered from (9.1)) is handed over to the original BM4 for row-by-row parent search, precisely restoring the given parent table. This does not include any parentless numerical matrices. The standard form belongs to this domain; the original expansion, as well as the subsequent $W$ and $\Sigma$, remain in this domain. The auxiliary form does not need to be reachable from the standard seed.

The last column $x$ has the highest parent behavior $r$, controls the parent $c=P_r(x)$, and the bad block width is $d=x-c$. Let

$$
\phi_b(i)=\begin{cases}i,&i<c,\\i+bd,&i\ge c.\end{cases}
$$

After taking the original $[n]$, the old prefix remains unchanged; the $b$th copy, $1\le b\le n$, has its parent as

$$
\begin{aligned}
P'_q(i+bd)&=\phi_b(P_q(i))&& (c<i<x),\\
P'_q(c+bd)&=\phi_{b-1}(P_q(x))&& (q<r),\\
P'_q(c+bd)&=P_q(c)&& (q\ge r).
\end{aligned}\tag{9.2}
$$

The missing items remain missing. The formula is a copy of the original BMS parent table formula cited in the 2 section. From the recursive parent search check: The low coordinates of the first column of the first copy are kept as the old last column values, and the active rows and above are changed to control parent values. Subsequent copies follow the end-column template of the previous document with (9.2)), and the corresponding parent and child subtrees that are not the first column are also transported. Inductively from the row and block numbers, we obtain (9.2) and (9.1), while maintaining normativity.

For each $M$, $M[0]$, and $M[1]$, they are prefixes of $M[n]$, and $n\ge1$. The expansion of the positive indices of non-zero terminal columns does not reduce the number of columns; zero-terminal columns delete exactly one column. The following quantitative comparisons will use these **Actual Expansion Properties**, without using the general principle that "the larger the ordinal, the longer the fixed-index calculation".

## A complete simulation and counting of the ancestor coverage of 10

### 10.1 Definition and Control Preparation

It is called $M$ being covered by the $N$ ancestor, which means there exists a strictly increasing sequence mapping $f$, which maps the last column to the last column, and

$$
p\prec_q^M i\Longrightarrow f(p)\prec_q^N f(i).\tag{10.1}
$$

Only the direct parent edges of the source are checked. The target may have additional columns, edges, and rows; the empty source takes an empty mapping.

Let the source end column be controlled as $(r,c)$. The target end column is controlled as $(R,p)$. It is covered by $R\ge r$. Define a preparatory operation: first take $[1]$, then repeatedly take $[0]$ to return to the original width. The prefix remains unchanged, and the number of the new end column is

$$
a'_x(q)=\begin{cases}a_x(q),&q<R,\\a_p(q),&q\ge R.\end{cases}\tag{10.2}
$$

This is a non-empty real descent, where at the coordinate $R$, the value strictly decreases, while the lower coordinates remain unchanged. The last column coordinates are constrained by a fixed prefix and a finite maximum value of the initial last column, therefore this operation of the same width cannot be performed indefinitely.

If $R>r$, it maintains all the necessary ancestors in the lower rows for the source columns. If $R=r$ but $p>f(c)$, then $f(c)\prec_r p$, the new source column inherits the $r$th ancestor from $p$, while still retaining the $f(c)$ and earlier necessary ancestors. The other source columns remain unchanged. Thus, as long as the target control is not $(r,f(c))$, preparation can continue and maintain coverage. It cannot lose its active row first, because the $f(c)$ must be retained. The finiteness ensures that it will eventually reach its destination.

$$
(R,p)=(r,f(c)).\tag{10.3}
$$

### 10.2 Synchronous Replication

When deleting the source columns, the target uses the image of the second-to-last source column, denoted by $[0]$. If the source columns are deleted and empty, the target is also left empty. Otherwise, prepare to (10.3)), taking the same positive index $n$ on both sides. Let the widths of the bad blocks be $d_M=x-c$ and $d_N=f(x)-f(c)$, respectively. The old prefixes are retained; the copy mapping is defined as follows:

$$
f_n(i+bd_M)=f(i)+bd_N\quad(c\le i<x,\ 1\le b\le n).\tag{10.4}
$$

It is strictly increasing. For (9.2), there are three categories of coverage checks: non-head columns are transported along with the original coverage chain; The first column continues the parent chain of the old last column at $q<r$. The control parent is the ancestor of these lower rows, so the cross-block chains continue at the same critical points. The first column inherits the ancestors of the old cut points when $q\ge r$ is reached, and these cut points have been covered by $f(c)$. Inductively from left to right along the copy, all the source parent chains are traced back to the target ancestor chain. If there are any unmatched tail columns in the target, they are cut off with $[0]$ to align the last column. The left side is not affected by truncation.

Therefore, every step of the source is simulated by a non-empty finite descent of the target, and the target uses only the index $0,1,n$. This proves that the simulation is an arbitrary coverage, without requiring that the source and target have any specific common generative history.

### 10.3 fills mixed indices with fixed indices

If $P$ is a prefix of $Q$, and the fixed $[n]$ trajectory of $Q$ ends at $n\ge1$, then this trajectory must pass through $P$: Each step retains the prefix of the deleted last column, with the width reduced by at most one column, so $P$ cannot be skipped in terms of width. Before reaching that width, $P$ itself is not modified.

Because $Q[0],Q[1]$ is a prefix of $Q[n]$, any descent that uses only $0,1,n$ is a subsequence of the fixed $[n]$ trajectory, and each true step occupies a non-empty interval. If the target fixed trajectory terminates, the simulation indicates that the source fixed trajectory also terminates, and there is

$$
\boxed{d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n).}\tag{10.5}
$$

The second formula also requires a count: for each source zero-terminating column, at least one column is deleted in the target; the number of columns does not decrease in the steps of non-zero-terminating indices, so the corresponding interval contains at least one target zero-terminating column deletion. The intervals of different source steps do not overlap, so they can be counted separately.

### The 10.4 non-standard auxiliary form also terminates

Let's denote the standard diagonal chain as

$$
\Delta_{k,m}=(0^k)(1^k)\cdots((m-1)^k)=B_{k+1}[m-1].\tag{10.6}
$$

Every standard parent formula with a height of at most $k$ and a width of at most $m$ is covered by $\Delta_{k,m}$: For any strictly increasing column mapping with aligned terminal columns, any earlier column in the target row is a ancestor. The standard BMS well-ordering guarantee ensures that the target terminates in descent, and thus (10.5) applies to these non-standard auxiliary formulas. More generally, any infinite expansion chain can be progressively simulated to be excluded.

In particular, there is a fixed downward termination for $R_h$; for $H\ge h$, each column is identically given as $R_h$ is covered by $R_H$, therefore

$$
d_1(R_h)\le d_1(R_H),\qquad s_{R_h}(1)\le s_{R_H}(1).\tag{10.7}
$$

This completes the counting termination used in sections 1, 4, and 8, without relying on Laver initialization.

## Change the width of the rows with 11

Take $k\ge2,m\ge3$. Apply $m-2$ times the "$[1]$ after cutting back to the original width" to the last column of $\Delta_{k,m}$. The last columns are transformed into

$$
((m-1)^{k-1},m-2),\ldots,((m-1)^{k-1},1).
$$

At this point, the highest row is the parent row. Take another $[1]$, and the width becomes $2m-2$. The first $k-1$ rows are exactly the complete diagonal chains $0,1,\ldots,2m-3$. From (10.5)

$$
s_{\Delta_{k,m}}(1)\ge s_{\Delta_{k-1,2m-2}}(1).\tag{11.1}
$$

On the other hand, $R_H[1]$ is

$$
(0^H)(1^H)(1^{H-1},0)(2^{H-1},1).
$$

Its columns 0, 2, 3 cover the row $H-1$ in the column $\Delta_{H-1,3}$. The width is iterated from 3 (11.1)), with the width being recursively determined by $m\mapsto2m-2$, thus

$$
\boxed{s_{R_H}(1)\ge s_{\Delta_{H-1-u,\,2+2^u}}(1)
\quad(0\le u\le H-2).}\tag{11.2}
$$

According to section 10.4, the right side also controls any standard auxiliary matrix that does not exceed that height and width.

## 12 precisely compiles FGH into Hardy

For the matrix $M$, define $W(M)$ as follows: add a full zero column at the beginning, increment the 0th coordinate of each original column by 1, and keep the other coordinates unchanged. Do not increase the number of rows. The parent table notation is: first add an empty column, the original empty column becomes $[0]$, and the original non-empty parent list $[p_0,\ldots,p_r]$ becomes $[p_0+1,\ldots,p_r+1]$. This is a standard parent table, but it is not claimed to be a standard reachable expression.

For any $n\ge0$, there exists a precise identity

$$
W(\varnothing)=Z,\qquad W(MZ)[n]=W(M)^{\frown(n+1)},\qquad
W(M)[n]=W(M[n])\quad(M\text{ has a nonzero last column}).\tag{12.1}
$$

In the second formula, for the active behavior on the 0 row, the bad root is the newly added first column, and the original block is retained with an additional $n$ copy added to it. In the third formula, the original active row remains unchanged, and the entire original parent sequence is incremented by 1. The first column will not be inserted between the original non-zero coordinates and their parents. In the 0 coordinate system, adding 1 does not change the original bad block difference and the high-row parent search. Therefore, the values remain the same item by item in the 9.2) coordinate system. It also holds that when $n=0$, both sides have corresponding column deletions.

Define the auxiliary Hardy computation

$$
\mathcal H_\varnothing(x)=x,\quad
\mathcal H_{MZ}(x)=\mathcal H_M(x+1),\quad
\mathcal H_M(x)=\mathcal H_{M[x]}(x)\quad(M\text{ has a nonzero last column}).\tag{12.2}
$$

Perform a well-founded induction on the standard $M$, (12.1) proves

$$
\boxed{\mathcal H_{W(M)}(x)=F_M(x),}\tag{12.3}
$$

Prove that the auxiliary computation terminates. For the empty formula and non-zero final column cases, direct substitution is used. If $M=AZ$, then first generate $x+1$ copies of $W(A)$. Each copy starts with a zero column, and bad blocks cannot cross this root, so they are executed independently. Each copy transforms the current input $y$ into $F_A(y)$, and the overall result is precisely $F_A^{\circ(x+1)}(x)$. It is not assumed that all non-standard Hardy computations terminate.

## 13 increases the row forest control parameter

### 13.1 Forest Evaluation

A single-row canonical matrix is a precedence depth list of a finite ordered forest. Let

$$
V_q(\varnothing)=0,\quad V_q(FG)=V_q(F)+V_q(G),\quad
V_q(\operatorname{node}(F))=q^{V_q(F)}.
$$

When the original index $[n]$ is fixed, it becomes $s_F(n)=V_{n+1}(F)$. Proof: Deleting the zero-end column reduces $V_{n+1}$ by 1, and the expansion of the non-zero-end columns remains unchanged. The latter assertion is $q^{a+1}=q\,q^a$ at the active parent node, and substituting it with the outer index and addition. The value at the endpoint is zero, thus the counting equation holds.

Let $F_x$ denote a single-chain forest with depth $0,1,\ldots,x$, and set

$$
e_0=1,\qquad e_{x+1}=2^{e_x}.
$$

Therefore, $s_{F_x}(1)=e_x$.

### 13.2 Diagonal row transformation and root template

$\Sigma(M)$ indicates adding a zero column, and then adding a new column with the 0 coordinate $1,2,\ldots,|M|$ to the original columns. The original coordinates are moved to a higher row. If the parent list of the original column with the $j$ index is $C$, the new parent list is

$$
[j]\mathbin{{}^\frown}[p+1:p\in C].\tag{13.1}
$$

It adds a new row, and the 0th row becomes a complete ancestral chain, while maintaining normativity.

Fix the non-zero last column matrix $M$, the original highest active row $r$, and the control parent $p$. Write

$$
\Sigma(M)=A B_0 C_0,\qquad d=|B_0|=|M|-1-p\ge1,\qquad R=r+1.
$$

In the $C_0$, the 0 row has a parent in the $B_0$ last column, the $R$ row has a parent in the $B_0$ first column. All defined parents are within the $B_0$, and there are no parents above the $R$. The previous point is obtained by the higher row ancestors, which are also lower row ancestors. The root template $C_b$ retains these internal parent numbers, and only replaces the block with the current length $d$ of the $B_b$.

For any finite row forest $F$, define the decoration $E_b(F)$ as follows: Each root of the forest is replaced with the complete $C_b$, and for non-roots, only the 0th row parent is retained, along with the image pointing to the corresponding forest parent; higher rows have no parents. The 0th row parent of each root is attached to the end column of the $B_b$th row, and non-roots continue to the left according to the original forest specification; the higher row parents of roots are linked back to $B_b$ along this lower row ancestor connection, so the decoration remains the standard parent table. Consider the state

$$
\text{frozen prefix}\ B_bE_b(F).\tag{13.2}
$$

### 13.3 Two Local Transfers

If the terminal node of the forest is not the root, the target column only has a parent in the 0th row. Bad blocks start from their forest parent and do not enter the $B_b$. From (9.2), fixing $[1]$ once, $E_b(F)$ is transformed into $E_b(F[1])$: The forest parents within the replication area move with the copies, while those outside remain fixed. If the first point of the replication area is the root of the forest, all of its higher parents are in the $B_b$ area, and the copies still use the same root template. The $B_b$ and freezing prefix remain unchanged.

If the end point of the forest is the root, and the target end column is $C_b$, the controlling parent is the first column with $B_b$, and the active behavior is $R$. Let $F^-$ delete the last root. Fix $[1]$ once, retain the old $B_bE_b(F^-)$, and copy the entire block. The copy header $d$ becomes $B_{b+1}$, followed by exactly $E_{b+1}(F^-)$: The parent of the root is in $B_b$, so it is moved to the new block; non-roots are transported according to the forest parent. Therefore, the new active state is

$$
\text{longer frozen prefix}\ B_{b+1}E_{b+1}(F^-).\tag{13.3}
$$

These two transitions each use the target $[1]$ only once. Therefore, each subsequent deletion in the activity forest generates a new bad block.

### The parent edge of the birth block with the symbol 13.4

When generating to $B_b$, select the original $A$ and $B_0,\ldots,B_b$, and skip the frozen forest columns. These columns have a column mapping that maintains direct parent relationships with $\Sigma(M[b])$.

Inductive reasoning for $b$. The base case $b=0$ involves deleting the old last column. When generating new blocks, the first column inherits from the parent of the current $C_b$ below $R$, thus being moved to the corresponding position within the previous block; it inherits from the parent of the old bad block's first column above $R$, and is transported back to the same shared prefix. The parents within non-first columns move with their copies, while the parents outside the block remain unchanged. This is precisely the formula for the next copy of (9.2)); the row at the 0 position also receives the last column of the previous bad block. The freezing forest step does not modify the selected blocks, and the induction holds.

When the active forest is emptied, the current $B_b$ last column also becomes the last column of the entire target. Therefore, the mapping is to cover the ancestors that are aligned with the last column. The total number of new blocks is...

$$
b=s_F(1).\tag{13.4}
$$

### 13.5 tail parameter chain

Take $F=F_x$, with the initial decoration being precisely $\Sigma(MZ^x)$. From (13.4)), its fixed orbits pass through a matrix that covers $\Sigma(M[e_x])$. For $x\ge1$, there is $e_x\ge2x$: $e_1=2$. By induction, use $2^{2x}\ge2(x+1)$. Therefore, $M[e_x]$ has at least $(e_x-x)d\ge x$ more columns after the prefix $M[x]$.

$\Sigma(M[e_x])$ also covers $\Sigma(M[x]Z^x)$: the prefix is identity, and the last $x$ parameter columns are mapped to the target's last $x$ column; these parameter columns only require the 0th ancestor row, and the target's complete chain provides all cross-void relationships. Using (10.5))

$$
\boxed{s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(M[x]Z^x)}(1)
\quad(x\ge1,\ M\text{ has a nonzero last column}).}\tag{13.5}
$$

Let $K(M,x)=s_{\Sigma(MZ^x)}(1)$. Hardy's successor steps satisfy the literal equation $K(MZ,x)=K(M,x+1)$, and the limit steps are such that (13.5) ensures that $K$ does not increase. Therefore, any Hardy computation that terminates at $(M,x)$ and ends at $(\varnothing,y)$, $x\ge1$, satisfies the conditions.

$$
\boxed{s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(Z^y)}(1)=e_y.}\tag{13.6}
$$

$\Sigma(Z^y)$ is a chain with a depth of $0,1,\ldots,y$. This formula retains the residues of the tower function, resulting not only in a weaker lower bound of $y$.

## 14 strong counting interface and round-by-round buffering

Let $\ell(x)=\lceil\log_2(x+2)\rceil$. For $r,x\ge1$, the matrix

$$
P_{r,x}=\Sigma(W(B_r)Z^x)
$$

There are rows with $r+1$ and columns with $x+4$. If $h=r+2+\ell(x)$, in (11.2) where $u=\ell(x)$, a diagonal chain with a height of $r+1$ and a width of $2+2^{\ell(x)}\ge x+4$ is obtained, thus covering $P_{r,x}$. Larger $h$ are processed using (10.7). Combining (12.3) and (13.6):

$$
\begin{aligned}
D(h)&\ge s_{R_h}(1)\ge s_{P_{r,x}}(1)\\
&\ge e_{\mathcal H_{W(B_r)}(x)}=e_{F_{B_r}(x)}.
\end{aligned}
$$

Thus, the unified strong interface for the second part is obtained.

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}\tag{14.1}
$$

Definition of row buffering

$$
\rho(x)=x+3+\ell(x).
$$

For the integer $x\ge1$, in (14.1) taking $r=x+1$ results in

$$
h\ge\rho(x)\Longrightarrow D(h)\ge e_{F_\Lambda(x)}.\tag{14.2}
$$

For the standard form, a well-founded induction is performed, and (1.1) yields $F_M(x)\ge x+1$. Therefore, when $x\ge2$, $y=F_\Lambda(x)\ge3$ follows. From $2^y\ge y+2$, $\ell(y)\le y$ is obtained, and thus $\rho(y)\le2y+3$. Additionally,

$$
e_y\ge2y+3\quad(y\ge3):
$$

The foundation is $e_3=16\ge9$; the inductive step is $e_{y+1}=2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$. Therefore

$$
\boxed{h\ge\rho(x),\ x\ge2\Longrightarrow
D(h)\ge e_{F_\Lambda(x)},\quad T(h)\ge\rho(F_\Lambda(x)).}\tag{14.3}
$$

This buffer payment accounts for all the logarithmic terms and additive constants of the next round. If only $D(h)\ge F_\Lambda(x)$ is used, it is not possible to directly perform the same iterative replacement.

## The initial long chain of 15 is sufficient to pay the inner constant

Write the constant of (2.5)) as a purely finite recursion:

$$
\begin{aligned}
g(x)&=x2^x,&u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C_{\rm line}&=w(w(1)).
\end{aligned}\tag{15.1}
$$

The certainty is derived by the induction of $m_k(2^x)=2^{u_k(x)}$; $m_\omega,m_{\omega+1}$ is respectively $v,w$ under exponential conjugation, hence $m_{\omega+2}(2)=2^{w(w(1))}$. Therefore, there is no need to change the chain length constant in the literature.

For $x\ge1$, $g(x)\ge2x$, and so on.

$$
g^{\circ2}(x)\ge g(2x)=2x2^{2x}\ge(x+1)2^{x+1}>F_2(x).
$$

These functions are strictly increasing, with $g^{\circ3}(1)=2048>256$. Derived from (1.3),

$$
t<g^{\circ514}(256)<g^{\circ517}(1).\tag{15.2}
$$

Set $b_0=g^{\circ258}(1)$. The direct calculation of the number of steps yields $u_1(1)=8$, and

$$
v(1)=u_2(1)=u_1(8)=g^{\circ256}(8)=b_0.
$$

By induction on $k$, each $u_k$ is strictly increasing, greater than the identity function, and non-decreasing with respect to $k$. Increasing the input also increases the initial value and the number of iterations. Therefore, $v,w$ also satisfies the same input properties. Thus,

$$
\begin{aligned}
C_{\rm line}&>w(1)=v(b_0)=u_{2^{b_0}}(b_0)\\
&\ge u_1(b_0)=g^{\circ2^{b_0}}(b_0)
=g^{\circ(2^{b_0}+258)}(1)\\
&\ge g^{\circ519}(1)>g^{\circ2}(t)\ge4t.
\end{aligned}\tag{15.3}
$$

In the case of iterative counts, it is only necessary to use $b_0\ge2048$. $t\ge2$ and $\ell(t)\le t$, therefore

$$
\boxed{h_0=C_{\rm line}+2\ge t+3+\ell(t)=\rho(t).}\tag{15.4}
$$

It is not necessary to determine the exact values of $D(3)$ and $T(3)$, nor to expand the decimal representations of any of the aforementioned large integers.

## The main theorem is obtained by merging 16.

Put

$$
x_0=t,\quad x_{i+1}=F_\Lambda(x_i),\qquad h_i=T^{\circ i}(h_0).
$$

By induction on natural numbers $i$, with (15.4), (14.3)), there holds that

$$
h_i\ge\rho(x_i),\qquad D(h_i)\ge e_{x_{i+1}}.\tag{16.1}
$$

Note: $x_{i+1}\ge x_i+1$, therefore this specific iteration sequence is strictly increasing; there is no need to assume the monotonicity of the general FGH subscripts, and there is even no need to prove the monotonicity of $F_\Lambda$ input.

Set $N=D(h_1)=D(T(h_0))$. From (16.1))

$$
N\ge e_{x_2}\ge x_2+1.\tag{16.2}
$$

Part 1: 8.3) provides

$$
q(5)>D(h_{N+1})\ge e_{x_{N+2}}\ge x_{x_2+3}.\tag{16.3}
$$

The last inequality is strictly increasing with $N+2\ge x_2+3$, $x_i$, and $e_y\ge y$. According to (1.2),

$$
x_{x_2+3}=F_\Lambda^{\circ(x_2+1)}(x_2)
=F_{\Lambda+1}(x_2),\qquad x_2=F_\Lambda(F_\Lambda(F_3(256))).
$$

Substitute (16.3)) to get

$$
\boxed{q(5)>F_{\Lambda+1}\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).}
$$

Proof completed.

## 17 Proof Scope and Dependencies

The conclusion is a paper inequality concerning **A specific finite integer** under ZFC + I3, and it does not claim to eliminate I3. It relies on the literature theorem listed in section 2; the proof of the remaining new lemmas is provided in this document.

The dependent order is as follows: The 9–13 section independently provides the BMS termination and strong counting interface; the 4–8 section presents the Laver endpoint budget and variable rounds feedback based on this terminationality; the 14–16 section deals with payment buffering and merging. The 10 section does not use Laver's lemma, so the text presents the first part without causing a circular proof.

In this document, two potentially confusing concepts are addressed separately: zero ports have no witnesses, so the proof in section 4 is about weak band preservation, rather than applying the complete BLS out of thin air; the new input chain is not necessarily a transport image, so the full insertion induction in the re-execution environment algebra is performed in section 7.3, without assuming the existence of inverse images.

The complete IBLP, IBLP 030, and any specified FGH value, as well as the statement "The internal structure is significantly stronger than the new notation of BMS," are not included in the conclusions of this theorem. The occurrence of $\Lambda+1$ is accurately derived from (16.2) having undergone at least $x_2+1$ iterations of $F_\Lambda$, and not merely inferred from the larger ordinal type to fix the indicator value. The finite script serves only as a local verification and is not the proof basis for any universal proposition in this paper.
