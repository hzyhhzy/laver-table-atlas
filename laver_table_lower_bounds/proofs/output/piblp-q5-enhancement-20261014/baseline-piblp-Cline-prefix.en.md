# pIBLP computation retains the original literature's long-chain constant · [中文版](baseline-piblp-Cline-prefix.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Let $S$ be the top row of nine pIBLP lines, and let $f_{\rm PP}$ be a function of [Parent package finite parameter recursion](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.md>) in the 3 section. Let $C=C_{\rm line}$ be the $f(p_{\omega+2},1)$ provided by the original Qi literature. The following proof...

$$
\boxed{f_{\rm PP}(S,1)\ge C.}
\tag{1}
$$

The proof only compares finite recursive values and uses inductive reasoning within the same practical BLS context. The assertion that "any two critical points belonging to the same $\operatorname{Iter}(j)$ can be extended into lined chains" is not used, as it goes beyond the scope of the Qi Lemma 2.11.

## Monotonicity of values within the same actual prefix

For the actual inputs allowed by the quantitative bridge $f_{\rm PP}$ and the current finite parameter $m$, if $Q\sqsubseteq P$ is a prefix of at least two lines and is used in implementations derived from the same actual BLS constraints, then

$$
f_{\rm PP}(Q,m)\le f_{\rm PP}(P,m).
\tag{2}
$$

First note: For any call to $f_{\rm PP}(R,x)$ that has a finite evaluation tree, the output is not less than the input $x$. By induction along the finite evaluation tree: zero terms are $x2^x\ge x$; ordinary recursive branches do not change the parameters; E-successor combines sub-calls with this property with a finite number of compositions. Here, we only discuss calls that are already defined in the current evaluation tree, without assuming that the fixed first tuple has a common linedness for all parameters.

Now, we make a strong induction on the finite potential $\Phi$ that is actually implemented, and at the same time prove that all valid current parameters and prefixes satisfy (2). We only need to prove $Q=\operatorname{cut}P$ first, and then proceed along the finite prefix string.

- Domain replication failure: Recursive definitions directly yield equations.
- Transient: The recursive input $R=M_{\rm PP}(P)$ has a smaller potential, and it is literally preserved.
$\operatorname{cut}P$. The actual points of this prefix and its owners are the constraints of the original BLS. Applying the inductive hypothesis to $R$ is sufficient.
- E-limit:$R=E_P(m)$ also has a smaller potential and retains $\operatorname{cut}P$.
Therefore, the same argument holds true.
- E-successor: Definition to denote the case where $x\mapsto f_{\rm PP}(\operatorname{cut}P,x)$
Iterate $2^m\ge1$ times. The value of the first call is the left endpoint of (2); each subsequent call does not reduce the input, so the final value is not less than the first call.

These are grammatical prefixes, with existing operations and finite numerical inductions; the proof does not create a new BLS with a different end, nor does it invoke any endpoint extension lemmas. The actual maintenance of M and E is achieved using the existing quantitative bridges. If the definitiveness of the fallback branch needs to be extended from the linedness of cut, then the column points that are both ends of the same parent BLS should still be strictly referred to according to the column point conditions applicable to that theorem; (2) does not expand upon this condition.

## From the first four lines to the literature pattern

Let $P_4=S[0]^5$ be, that is

```text
(1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2
```

All the M below are a raw short copy followed by a parent package scan, namely pIBLP's $[2]$. Every step of the full copy guard has been passed, and the additional propagation of the parent package is zero.

```text
P4:
(1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2

M1:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2)1

M2:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,*4,3,2,1,0)3

M3:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,4,3)1

M4:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,4,2,1,0)3

E1:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,3,2,1,0)3

E2:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,2,1,0)2(6,5,2,1,0)3

E3:
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2,1,0)3(5,2,1,0)2(6,2,1,0)2
```

The last lines of the three E inputs are $01245:3$, $01235:3$, $01256:3$, all of which are E-limit type $012an:3$. Therefore, the three recursions all call $E_P(1)$, with the parameter always being 1. It is not that E-successor arbitrarily replaces the iteration with a single E(1) at that point. The first four recursions are all transient M. The last term E3 is precisely $p_{\omega+2}$. So

$$
f_{\rm PP}(P_4,1)=f_{\rm PP}(p_{\omega+2},1).
\tag{3}
$$

The above finite array has been independently replayed. The total number of times M occurs four times, and E occurs three times, is within a direct finite range, without involving large orbits or numerical evaluations.

## The complete recursive closure of a small pattern family

$p_0$ is fixed in two rows, $01:1,012:1$. For $n\ge0$, $p_{n+1}$ is added after $p_n$ with $012(n+3):2$. Therefore, $p_n$ has $n+2$ rows.

$p_\omega$ is a four-line text.

```text
01:1 012:1 0123:2 01234:3
```

$p_{\omega+k+1}$ is added to the corresponding E-successor lines after $p_{\omega+k}$. All positive finite successors of this family and $p_{\omega+k}\;(k>0)$ are E-successor; $p_\omega$ is E-limit, and it is directly derived from the raw E formula.

$$
E_{p_\omega}(m)=p_{2^m}.
\tag{4}
$$

The reason is that $\operatorname{cut}p_\omega=p_1$, E uses the threshold 3, and each auxiliary replication doubles the number of successor rows starting from the 3 row; after performing the specified $m$ times, it reaches the $2^m$ row. All marks are empty, and the auxiliary E does not perform native or mark scanning.

All copies of the E type have a starting point of 1, with the smallest address being 0. The only lower address, 0, is within the control line, while the rest of the addresses are located in the translation area. Therefore, the complete copy has a fully defined guard. The entire $f_{\rm PP}$ evaluation closure only uses the E branches of this family, without any transient, PP scanning, or fallback mechanisms.

Put

$$
\begin{aligned}
g_0(x)&=x2^x,&u_0(x)&=g_0(x),\\
u_{n+1}(x)&=u_n^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x).
\end{aligned}
$$

Recursively defined and obtained from (4) literally

$$
f_{\rm PP}(p_n,x)=u_n(x),\quad
f_{\rm PP}(p_\omega,x)=v(x),\quad
f_{\rm PP}(p_{\omega+1},x)=w(x),
$$

$$
f_{\rm PP}(p_{\omega+2},1)=w^{\circ2}(1)=w(w(1))=C.
\tag{5}
$$

Combining (2), (3), (5), we obtain (1). Here, only a non-strict comparison is obtained. If one claims that pIBLP strictly increases the original numerical constant, additional strict numerical increments must be provided.
