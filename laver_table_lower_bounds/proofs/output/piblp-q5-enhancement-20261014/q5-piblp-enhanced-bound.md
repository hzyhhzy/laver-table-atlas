# The q5 introduced by pIBLP enhances the lower bound. · [中文版](q5-piblp-enhanced-bound.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Assuming ZFC + I3, fix the same generator and its algebra $\operatorname{Iter}(j)$. This paper shows that the finite parameter recursion of pIBLP actually returns a BMS row count feedback, resulting in a lower bound that is strictly greater than the previously recorded FGH lower bound.

Let $\Lambda=\lim(\mathrm{BMS})$, $g=F_\Lambda$, and let $C=C_{\rm line}$ be the long-chain constant from previous literature. Then

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(2^C))\bigr).}
\tag{A}
$$

Use $(\Lambda+\omega)[x]=\Lambda+(x+1)$. Here, $q(5)$ is the order parameter for the first occurrence of $32$ in the first row of the ordinary binary Laver table, and it does not represent the number of elements in the table $2^{q(5)}$. The conclusion is based on paper derivations and has not yet been formalized in Lean.

Set $S$ as the current nine-row seeds, $G(m)=f_{\rm PP}(S,m)$, and set

$$
X=g(g(2^C)),\qquad e_0=1,\quad e_{r+1}=2^{e_r}.
$$

The following specified calls are defined, and

$$
\boxed{q(5)>2^{G^{\circ(e_X+1)}(1)}.}
\tag{B}
$$

$G$ is a recursive growth with a finite number of parameters for the parent package, and it does not fix the total number of steps for `[2]`, nor does it equal FGH as defined by pIBLP. This paper does not compare the magnitudes of (A) and (B) at the right-hand end.

## 1 Axiomatic Conditions and Practical Implementation

Using I3 to embed $j:V_\lambda\to V_\lambda$, all row owners, segments, and owners after mapping remain in the same $\operatorname{Iter}(j)$. The distinction between application $a(b)$ and ordinary composition $a\circ b$ is always maintained.

The global critical points are enumerated as $\gamma_0<\gamma_1<\cdots$, continuing with $\kappa_4=\gamma_{q(5)-1}$. A $M$-lined $(\kappa_0;\kappa_1,\ldots,z)$ witness, if it satisfies $z<\kappa_4$, is given the same algebraic count as $\gamma_{2^M}\le z$. Therefore,

$$
q(5)>2^M.
\tag{1}
$$

The actual first three points of the nine-row seed $S$ are $(\kappa_0,\kappa_1,\kappa_2)$, with cap being $\theta_6<\kappa_4$. The initial linedness parameter is 1. Information on its ordinary rows, Sat, proper marks, positive sources, and natural membership truncation certificates can be found in [Seed complete certificate](<../iblp-030-laver-20261014/same-owner-L3-sat-closure.md>).

[Parent package quantitative theorem](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.md>) proves the computational definiteness and linedness for the current implementation and finite parameters. Therefore, $L=G(1)$ is defined, and the $(\kappa_0;\kappa_1,\ldots,\theta_6)$ of the actual $L$-section chain is given. It is not assumed that $G(m)$ is fully defined for all integers.

## 2 pIBLP provides a strictly longer initialization

Let $P_i$ be the first $i$ rows of $S$, and denote it as $H(m)=f_{\rm PP}(P_4,m)$. The existing small pattern reduction strictly gives $H(1)=C$, where $C$ can be defined without the term "embedding".

$$
\begin{aligned}
g_0(x)&=x2^x,& u_0(x)&=g_0(x),\\
u_{r+1}(x)&=u_r^{\circ2^x}(x),& v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),& C&=w(w(1)).
\end{aligned}
\tag{2}
$$

A key finite auxiliary replication is

```text
P4 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2
P5 = P4(5,3,2,1,0)3
E_P5(1) = P4(5,2,1,0)2(6,*5,2,1,0)2
R = P4(5,2,1,0)2
```

$P_5$ is a prefix of E-limit; $R$ is a prefix of $E_{P_5}(1)$, and it is also a prefix of E-successor, satisfying $\operatorname{cut}R=P_4$. Both instances of the guard are copied intact. The auxiliary E does not scan native or marks during copying.

In the same actual realization, the quantitative function does not decrease before the prefix. This property is derived from the finite table potential, without using the monotonicity of its logarithmic parameters. Therefore

$$
\begin{aligned}
L&\ge f_{\rm PP}(P_5,1)
=f_{\rm PP}(E_{P_5}(1),1)\\
&\ge f_{\rm PP}(R,1)
=H^{\circ2}(1)=H(C).
\end{aligned}
$$

Every call with a formally defined certificate satisfies $f_{\rm PP}(P,m)\ge m2^m$, which can be proven by induction based on finite evaluation trees. Therefore

$$
\boxed{L\ge H(C)\ge C2^C>C.}
\tag{3}
$$

The definition of $H(C)$ comes from the construction of the E-successor double block, and it is not assumed that the same triple can support any parameter. The complete derivation and finite array certificates can be found in [Strictly initialized increment](<audit-piblp-strict-Cline.md>).

## 3 will add the chain length back to the BMS row number

Following the actual application term $E=L_3(K)$, its proven point image is

$$
E(\kappa_0)=\kappa_2=k,\quad E(\kappa_1)=\theta_6=a,\quad
E(\theta_6)=\tau=b<\theta_7=c<\kappa_4.
\tag{4}
$$

Take all the $L$-chains in the 1 section and transform them into $E$-images, resulting in the $(k;a,\ldots,b)$ section of $L$-chains. Thus, [Unified Front-End Insertion Lemma](<../iblp-laver-bms-20261013/lined-front-insertion.md>) provides a high level of

$$
h_*=L+2
\tag{5}
$$

The closed compatible fan has a closure strictly less than $b$. There is no problem with the end of the input chain being precisely $b$: the closure of the output of the lemma is strictly less than this end.

Let

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil.
$$

From $C\ge3$ and (3),

$$
\rho(2^C)=2^C+C+4\le C2^C+2\le h_*.
\tag{6}
$$

Therefore, the new legitimate entry is not just the original $C+2$ row, but is sufficient to cover the cost of the input $2^C$ and all its rows.

## 4 has an accurate interface with recursive feedback

Let $B_r=(0^r)(1^r)$, $R_h=(0^h)(1^h)(1^h)$, and denote $D(h)$ as the number of steps in which $R_h$ repeatedly takes the original BM4 `[1]` until it empties, denoted as $T(h)=D(h)+2$. The original BM4 `[1]` is equal to the `[2]` displayed by the new parent table.

Use the following two existing interfaces.

First, [Strong Forest Counting Buffer](<../iblp-030-laver-20261014/nested-bms-FGH-bound.md>) indicates

$$
h\ge\rho(x),\quad x\ge2
\ \Longrightarrow\ 
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{7}
$$

Secondly, define the finite layer natural template.

$$
U_0=T,\qquad
U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),\qquad
m(h)=\lfloor\log_2D(T(h))\rfloor.
$$

For any **The system has been actually initialized.** of height $h\ge3$, the entrance fan with a seal below $b$, the [Recursive template and short transport endpoint theorem](<../iblp-030-laver-20261014/small-period-endpoint-Sf.md>)th section is given as 4.1

$$
q(5)>D(U_{m(h)+1}(h)).
\tag{8}
$$

The old text often used the notation $h\le C+2$, which was merely an initialization range provided at that time. The template proof itself only reads the actual entrance fan. In the 3 section, this certificate has been re-supplied for the $h=h_*$ case, so no numerical inequality limited to the old height has been arbitrarily extended here.

The endpoint construction begins with the generation of a finite integer $m(h)$ by a single independent $T(h)$. Subsequently, high common root chains of corresponding lengths are constructed, and finally, the template is executed. This approach ensures that the length of the chain does not depend on the final output, and it does not require any chain of any length to exist at the same endpoint. The naturalness of the template's overall context allows for any global input fan, rather than only the image of old fans.

## 5 obtains the limit plus omega of the FGH bound from the number of feedback layers

Let $J_i(x)=F_{\Lambda+i}(x)$ be, that is
$J_0=g$, $J_{i+1}(x)=J_i^{\circ(x+1)}(x)$.
The finite layer induction is given by (7)

$$
h\ge\rho(x),\ x\ge2
\ \Longrightarrow\ U_i(h)\ge\rho(J_i(x)).
\tag{9}
$$

In the inductive step, let $N=D(U_i(h))+1$, and simultaneously track $U_i^{\circ j}(h)\ge\rho(J_i^{\circ j}(x))$. Since (7) has $N\ge x+1$; additional iterations are processed along the same strict increase trajectory, without the need to assume the monotonicity of $U_i$'s input.

For any valid entry $h\ge\rho(x)$, set $x_2=g(g(x))$. Use (7) twice to obtain

$$
D(T(h))\ge e_{x_2},\qquad m(h)\ge e_{x_2-1}\ge x_2+1.
\tag{10}
$$

Here, $x\ge2$, so $x_2\ge4$. Expand the outermost layer $U_{m+1}(h)=U_m^{\circ N}(h)$. The first round is completed by (9), which has increased the height to at least $\rho(x_2)$; there is at least one more round to come, and (9) can be used again for a fixed input $x_2$. Therefore, (7), (8) provide the solution.

$$
q(5)>D(U_{m+1}(h))>J_m(x_2)
\ge J_{x_2+1}(x_2)=F_{\Lambda+\omega}(x_2).
\tag{11}
$$

For detailed additional iterations and endpoint audits, please refer to [Recursive Feedback FGH Transformation](<audit-recursive-corridor-FGH.md>). Substitute $h=h_*$ and $x=2^C$ into (11), which yields (A) from (6).

## 6 A strict comparison with the previously defined FGH boundaries

Let $t=F_3(256)$. It has been proven that $C>4t$, where
$F_2(x)=(x+1)2^{x+1}-1$, $F_3(256)=F_2^{\circ257}(256)$.
The strict comparison obtained in this case is

$$
\begin{aligned}
F_{\Lambda+\omega}(g(g(2^C)))
&>F_{\Lambda+\omega}(g(g(t)))\\
&>F_{\Lambda+1}(g(g(t))).
\end{aligned}
\tag{12}
$$

The second step can be carried out by comparing each finite successor layer on the same input. The first step requires specialized input comparison, and it is not assumed that any FGH is monotonic directly from $2^C>t$.

The fundamental sequences of a standard BMS retain the prefix for column deletion, and $P[x]$ is a prefix before the sequence $P[y]$ ($x\le y$). Additionally, there is a well-founded inductive proof for: $F_P(x)\ge x+1$, FGH does not reduce the prefix, and $F_P(y)\ge F_P(x)+(y-x)$. Furthermore, $B_s[n]=(0^{s-1})(1^{s-1})\cdots(n^{s-1})$ (after removing the highest row with all zeros), and $n\ge1$, have their first two sequences as $B_{s-1}$. From this, it is specifically proven that $g$ has a strictly increasing input, and then it is proven that each of the $J_i$ and $x\mapsto J_{x+1}(x)$ have a strictly increasing input, proving (12). The complete induction is presented in [BMS diagonal input comparison](<audit-BMS-diagonal-input-monotonicity.md>).

If you do not want to retain the literature constant $C$ in the formula, you may conservatively relax it to

$$
\boxed{q(5)>
F_{\Lambda+\omega}\!\left(
F_\Lambda\!\left(F_\Lambda\!\left(2^{F_3(256)}\right)\right)\right).}
\tag{13}
$$

These comparisons are directed at the explicitly stated right-hand side of FGH. It is not claimed that (A)) has exceeded any implicit recursive lower bounds that have not been developed before, such as the old parameter values of all $D(U_{m(h)+1}(h))$.

## Reproducible pIBLP numerical feedback with 7

Starting from the actual fans that are at a height of $T(h_*)$ and have a sealing below $c$, the actual chains are supplied with a length of [Constructing along long chains with feedback](<../iblp-030-laver-20261014/lined-feedback-corridor.md>) and a fundamental sequence of $N=D(T(h_*))$.

$$
\operatorname{crit}(Q_i)=k,\quad Q_i(k)=u_i,\quad Q_i(u_i)=u_{i+1},
\qquad \theta_6<u_0<\cdots<u_N<\kappa_4.
\tag{14}
$$

Each $Q_i$ is fixed by a $\kappa_0,\kappa_1$. $Q_i(S)$ is the actual realization of the same grammatical seed, with the first three points being $(\kappa_0,\kappa_1,u_i)$, and cap being $Q_i(\theta_6)<u_{i+1}$. All marks and natural truncation certificates are taken together.

First, use $S$ to obtain a low-radical chain with $G(1)$-lined structure. Extend the end of this chain to $u_0$, and then use $Q_0(S)$ to obtain the parameter $G(G(1))$. Repeat this process indefinitely to obtain the result.

$$
q(5)>2^{G^{\circ(N+1)}(1)}.
\tag{15}
$$

The definitiveness of each invocation is determined by the actual certificate for that instance. Endpoint extension only replaces the last segment of the separately carried linedness witness, without altering the owners or marks of the seed.

The global connection between any critical points required here comes from the standard fact recorded by [Dougherty, Article 2, Beginning of 3 Section](https://arxiv.org/pdf/math/9503204#page=10): $e_n=j_{(2^n)}$ satisfies
$\operatorname{crit}(e_n)=\gamma_n$, $e_n(\gamma_n)=\gamma_{n+1}$.
By finite induction, with $L_{a,a+1}=e_a$, $L_{a,b+1}=e_b(L_{a,b})$, it is possible to have
$\operatorname{crit}(L_{a,b})=\gamma_a$, $L_{a,b}(\gamma_a)=\gamma_b$.
This completes the necessary connection; It is not possible to simply quote the Lemma Qi 2.11, which applies to the same BLS column points. For a complete proof of the feedback, see [pIBLP Self-Feedback](<quant-self-feedback.md>).

Given (6), (7), ($N\ge e_{g(g(2^C))}=e_X$), in (14), only the first $e_X$ segments are taken, resulting in (B). Therefore, the existing pIBLP interface no longer uses $G(1)$ just once, but can use a finite number of self-compositions with a two-layer tower BMS to calculate the results diagonally.

## 8 Conclusion Range and Verification

(3) is the true pIBLP initialization increment; (A), (12) are the newly added explicit FGH lower bounds and strict comparisons; (B) retains more pIBLP self-feedback structures. They still do not convert the order type of the entire $S$ into FGH, nor have they proven that the FGH of the original IBLP $I[0][2]$ or $I[0][3][0]$ is controlled by $q(5)$. The well-orderliness of the full indicator pIBLP is not a premise of this paper.)

The finite verification includes a single P5 auxiliary replication, as well as marks, short transport endpoints, BMS two-column expansion formulas, and adjacent fundamental term prefixes. These are merely finite interface checks; the full conclusion comes from the above inductive reasoning and the listed paper theorems. No giant fixed index reductions are performed, nor are any FGH large numbers actually evaluated.
