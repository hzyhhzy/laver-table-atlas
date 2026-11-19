# Audit of FGH numerical conversion for recursive corridors · [中文版](audit-recursive-corridor-FGH.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Under the premise that the existing corridor endpoint theorem and the BMS strong buffer estimate hold, it can be strictly deduced

$$
\boxed{q(5)>F_{\Lambda+\omega}\!\left(F_\Lambda(F_\Lambda(F_3(256)))\right).}
$$

Here, it is agreed that $(\Lambda+\omega)[x]=\Lambda+(x+1)$. This specific value strictly exceeds the previous $F_{\Lambda+1}(F_\Lambda(F_\Lambda(F_3(256))))$. The proof does not use $F_\Lambda$ to determine the monotonicity of the input, nor does it directly infer the computational length from the notation order type.

## Existing input

From the [Short Transport Endpoint Proof](<../iblp-030-laver-20261014/small-period-endpoint-Sf.md>) section on the 4th chapter, the following established natural number conclusions are used. For the high $h\ge3$ supported by the existing entrance fans, let

$$
R_0=T,\qquad
R_{i+1}(h)=R_i^{\circ(D(R_i(h))+1)}(h),\qquad
m(h)=\lfloor\log_2 D(T(h))\rfloor,
$$

Then

$$
q(5)>D(R_{m(h)+1}(h)). \tag{1}
$$

From [Strong counting buffer](<../iblp-030-laver-20261014/nested-bms-FGH-bound.md>) usage

$$
\begin{gathered}
e_0=1,\quad e_{n+1}=2^{e_n},\quad
\ell(x)=\lceil\log_2(x+2)\rceil,\quad \rho(x)=x+3+\ell(x),\\
x\ge2,\ h\ge\rho(x)
\quad\Longrightarrow\quad
D(h)\ge e_{F_\Lambda(x)},\quad T(h)\ge\rho(F_\Lambda(x)).
\end{gathered}
\tag{2}
$$

Finally, use the existing initialization

$$
t=F_3(256),\qquad h_0=C_{\rm line}+2\ge\rho(t), \tag{3}
$$

The highly $h_0$ entrances are actual constructs of finite evidence. The following applies only to this legitimate entrance with (1).

## Finite successor layer buffer simulation

Definition

$$
G_0(x)=F_\Lambda(x),\qquad G_{i+1}(x)=G_i^{\circ(x+1)}(x).
$$

Therefore, $G_i(x)=F_{\Lambda+i}(x)$. Well-founded induction and finite iteration yield

$$
G_i(x)\ge x+1. \tag{4}
$$

For $x\ge1$, the number of iterations is $x+1\ge2$, so

$$
G_{i+1}(x)>G_i(x). \tag{5}
$$

Here, we only use $G_i(y)>y$: the result of the first call is $G_i(x)$, and the result of the second call is strictly greater than this number. There is no need to compare the values of $G_i$ at two different input points.

**Buffer Lemma.** holds for all finite $i$, $x\ge2$, and $h\ge\rho(x)$.

$$
R_i(h)\ge\rho(G_i(x)). \tag{6}
$$

Inductive reasoning for $i$. The zeroth layer is (2). Suppose the $i$th layer holds, set

$$
N=D(R_i(h))+1,\qquad h_j=R_i^{\circ j}(h),\quad
y_j=G_i^{\circ j}(x).
$$

By repeatedly applying the inductive hypothesis, the same invariant is obtained for all finite $j$.

$$
h_j\ge\rho(y_j). \tag{7}
$$

Especially $R_i(h)\ge\rho(G_i(x))$. Applying (2) to the input $G_i(x)$ yields

$$
N\ge e_{G_0(G_i(x))}+1\ge x+1. \tag{8}
$$

Also, from (4),$y_j$), it increases strictly with $j$; due to the monotonicity of $\rho$ with integers,

$$
R_{i+1}(h)=h_N\ge\rho(y_N)
\ge\rho(y_{x+1})=\rho(G_{i+1}(x)).
$$

This proof shows (6), and explicitly handles additional iterations. The entire proof does not assume that $R_i$ or $G_i$ is monotonous with respect to the input.

## Use the computed depth to retain the input after two warm-up rounds

Fix the $h=h_0$, and denote as follows:

$$
x_0=t,\quad x_1=G_0(t),\quad x_2=G_0(G_0(t)),\quad m=m(h).
$$

By applying (2) twice,

$$
T(h)\ge\rho(x_1),\qquad D(T(h))\ge e_{x_2}.
$$

Because $e_{x_2}=2^{e_{x_2-1}}$

$$
m\ge e_{x_2-1}\ge x_2+1. \tag{9}
$$

The last elementary estimate holds for $x_2\ge4$: $e_3=16\ge5$, and it is generalized by $e_{n+1}=2^{e_n}$. Here, $t\ge2$, therefore $x_2\ge4$.

Now unfold the outermost layer

$$
R_{m+1}(h)=R_m^{\circ N}(h),\qquad N=D(R_m(h))+1.
$$

The first round is given by (6) giving $R_m(h)\ge\rho(G_m(t))$. By (5), $m\ge1$, and $G_1(t)=G_0^{\circ(t+1)}(t)$, there is

$$
G_m(t)\ge G_1(t)\ge G_0^{\circ2}(t)=x_2. \tag{10}
$$

Here, the last one proceeds along the same $G_0$ trajectory, with only strict increments at each step. Therefore, the first round has already made the current height at least $\rho(x_2)$. Furthermore, by (2), $N\ge2$.

Starting from the second round, each round can re-use (6) for **Fixed target input $x_2$**, resulting in

$$
R_m^{\circ j}(h)\ge\rho(G_m(x_2))\qquad(2\le j\le N). \tag{11}
$$

The conditions required for induction remain valid. Since $G_m(x_2)>x_2$, the right-hand side is at least $\rho(x_2)$. Using (2) last time for (11), combined with (1), we obtain

$$
q(5)>D(R_{m+1}(h))\ge e_{G_0(G_m(x_2))}>G_m(x_2). \tag{12}
$$

From (5), (9),

$$
G_m(x_2)\ge G_{x_2+1}(x_2)
=F_{\Lambda+\omega}(x_2).
$$

Therefore

$$
\boxed{q(5)>F_{\Lambda+\omega}\!\left(F_\Lambda(F_\Lambda(F_3(256)))\right).} \tag{13}
$$

## A strict comparison with the original numerical domain

The old right-hand side is $G_1(x_2)$. The new right-hand side is $G_{x_2+1}(x_2)$. Because $x_2+1>1$, the same input is reused (5) to obtain)

$$
F_{\Lambda+\omega}(x_2)=G_{x_2+1}(x_2)>G_1(x_2)
=F_{\Lambda+1}(x_2). \tag{14}
$$

Therefore, (13) is indeed strictly stronger on the specific inputs at this point. The strictness only uses the point-state growth of the finite successor layer, without using the unproven monotonicity of $F_\Lambda$ inputs.

This is a numerical enhancement with an existing recursive corridor; it does not assume that all the indicators of pIBLP, such as well-order, complete $I[0][2]$ embedding, or some structural hyper-BMS notation, are proven prerequisites.
