# Marking phase: Preservation of endpoint prefixes and relocation · [中文版](marked-prefix-rebase.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. The goal is to first use markings and completion to build up a sufficiently strong finite structure, and then switch to simpler unmarked rules. The following proof demonstrates a parameter scaling operation that can strictly preserve the Laver periodic endpoint, and provides finite certificates that actually reach the standard root. What is produced are large **Linedness parameter**, and it has not yet been proven that BMS seeds with the same number of rows are generated. Therefore, it cannot be considered as the completion of the BMS[10] lower bound being achieved.

Throughout the text, the same I3 is used for embedding $j$. All embeddings and all instances of linedness belong to the same $\operatorname{Iter}(j)$. The classes of marked certificates $\mathcal C$, natural truncation, and Sat conditions follow the conventions of [Finite-parameter quantitative bridge](<marked-BLP-quantitative-transfer.md>). Complete lines include implicit ends; the core does not include them.

## General Relocation Lemma

Let $P\in\mathcal C$ have $n$ rows, with the last row being complete.

$$
s_n=(0,1,2,a,n,n+1),\qquad \ell_n=2,\qquad 3\le a<n.
\tag{1}
$$

This is a long line of ordinary BLP, not a limit line with step size 3. Let the last owner be $J$, and the global last cardinality be $\Theta=\theta_{n+1}$. Let

$$
q=p.\mathrm{del}.
$$

Assume that there are already testimonies within the same $\operatorname{Iter}(j)$, indicating

$$
(\theta_0,\theta_1,\theta_a)\quad\text{is }M\text{-lined}.
\tag{2}
$$

**Lemma.** Exist $R\in\mathcal C$ ， Its literal pattern is exactly $q$. and

$$
R.\theta_0=\theta_0,\quad R.\theta_1=\theta_1,\quad
R.\theta_2=\theta_a,\quad R.\Theta=\Theta,\quad R.m=M.
\tag{3}
$$

Additionally, $R<P$, where the comparison is based on the final cardinality and bounded application relationships. The $R$ here is not a conventional column deletion implementation: the end of a conventional column deletion is $\theta_n$, and the end after relocation remains $\Theta$.

### Constructing auxiliary embeddings

Taking the original second line owner $G$, thus

$$
G:\theta_0\longmapsto\theta_1\longmapsto\theta_2
  \longmapsto\theta_3.
$$

If $a=3$, take $G_a=G$. If $a>3$, use the conclusion from [Lemma 2.11](https://arxiv.org/html/2501.06733v5)'s naming point transport, and take $H$ to make

$$
\operatorname{crit}(H)=\theta_3,\qquad H(\theta_3)=\theta_a,
$$

Let $G_a=H(G)$. The use of this lemma involves only two named points of the original BLS; it does not presuppose that any subsequence of critical points can be realized. Apply the identity to

$$
G_a:\theta_0\longmapsto\theta_1\longmapsto\theta_2
  \longmapsto\theta_a.
\tag{4}
$$

The formula (1) describes the four sides.

$$
J(\theta_0)=\theta_2,\quad J(\theta_1)=\theta_a,\quad
J(\theta_2)=\theta_n,\quad J(\theta_a)=\Theta.
\tag{5}
$$

Let $K=J(G_a)$. From (4), (5),

$$
\boxed{
\operatorname{crit}(K)=\theta_2,\qquad
K(\theta_2)=\theta_a,\quad K(\theta_a)=\theta_n,\quad
K(\theta_n)=\Theta.}
\tag{6}
$$

In particular, $K$ is fixed to $\theta_0,\theta_1$.

### Transporting the entire prefix

For $0\le i\le n$, $1\le i<n$, define

$$
R.\theta_i=K(\theta_i),\qquad R.j_i=K(j_i).
\tag{7}
$$

Apply $K$ to the entire configuration $P.\mathrm{del}$. The application identities preserve strict increase and all ordinary row edges. Equation (6) gives precisely the three points and the endpoint in (3).

For a marked element, let its actual factor word be

$$
W=j_{v_0}\circ\cdots\circ j_t.
$$

Its literal trace in the tail prefix remains completely unchanged. After the transport, the owner and factors are respectively $K(j_i)$ and $K(j_{v_r})$, and the new nature is exactly

$$
\begin{aligned}
\Delta_R
&=\bigl(K(j_{v_0})\circ\cdots\circ
        K(j_{v_{d-2}})\bigr)(K(\theta_{t+1}))\\
&=K\!\left((j_{v_0}\circ\cdots\circ j_{v_{d-2}})
               (\theta_{t+1})\right)
=K(\Delta_P).
\end{aligned}
\tag{8}
$$

Here, $d$ represents the number of factors, with $v_{d-1}=t$ being the case for single factors. When there are no factors, the prefix compound is empty. Therefore, $j_i\equiv_{\Delta_P}W$ transport is $K(j_i)\equiv_{\Delta_R}K(W)$. It is not appropriate to arbitrarily replace nature with $\theta_{y+1}$, nor is it necessary to mark the presence of internal adjacency.

Proper, exact trace, PosSource, and Sat are all properties of the invariant prefix pattern $q$. New linedness witnesses are directly configured using (2); these witnesses do not have to be $K$-like of the old witnesses. Thus, a complete $R\in\mathcal C$ is obtained.

### Strictly decreasing

The last owner of $R$ is

$$
R.J=K(j_{n-1})=(J(G_a))(j_{n-1}).
\tag{9}
$$

This is a sequence of two applications starting from $J$. The critical point of the intermediate owner $K$ is $\theta_2<\Theta$, and the critical point of the final owner is also lower than $\Theta$ in the actual last line. The final cardinality remains $\Theta$, hence $R<P$. There is no increase in the cycle endpoints, nor is there any generation of new elements.

## Available magnification parameters

The formula (2) can be provided by quantitative theorems with shorter prefixes. For example, forget the marks only when calling the ordinary theorem.

$$
M=f\bigl(\operatorname{forget}(p|(a-1)),m\bigr)
\tag{10}
$$

Given by Theorem Qi 2.25; here the final cardinality of the prefix is precisely $\theta_a$. If we use the proven quantitative theorem for marked versions, it can also be used.

$$
M=f_\star(p|(a-1),m).
\tag{11}
$$

The invocation of the ordinary theorem to obtain (10) does not require the permanent deletion of the marks in the actual certificates; these marks are still transported according to (8).

The simplest case is $a=3$. The prefix has only a fixed first two rows, directly derived from [Lemma 2.4](https://arxiv.org/html/2501.06733v5).

$$
\boxed{m\longmapsto g(m)=m2^m.}
\tag{12}
$$

Therefore, when the last line has the core $(0,1,2,3,n)$ and the step size 2, the literal line can be deleted, the remaining pattern can be repositioned, and the parameter can be increased from $m$ to $g(m)$, while maintaining the original end. There is no definition of 'repeating M until some unknown moment' here.

This is a new type of **Semantic Certificate Transformation**. It is not claimed to be a step forward from the original IBLP, nor is it claimed to be $f_\star(p,m)=f_\star(q,g(m))$. Changing the certificate and proving a numerical identity for a specific recursive function are two different things.

## A clear repeating block formula

Let the last two lines of the pattern be

$$
\begin{array}{c|c|c}
 &\text{core}&\text{step size}\\ \hline
n-1 &(0,1,2,3,n-1)&2\\
n &(0,1,2,n-1,n)&3
\end{array}
\qquad n\ge5,
\tag{13}
$$

In the penultimate line, the only mark is 3. The first $n-2$ behavior is denoted as $q$.

Mark the last line with $E(m)$, and copy the anchor point to $a=n-1>3$. Assist in copying and fixing.
0. 1, 2, 3, translate the remaining coordinates. Therefore, the result of $E(m)$ is $q$ followed by $2^m$.
Rows of exactly the same type:

$$
(0,1,2,3,r),\quad \ell_r=2,\quad \operatorname{marks}_r=\{3\}.
\tag{14}
$$

Here, "identical" refers to shapes that are the same except for the last column symbol $r$. Each auxiliary replication doubles the size of the block, and it can be derived by an inductive argument with a long row starting from $E(0)$; the mark 3 follows a fixed lower branch, which is still retained.

Application item by item (The relocation of 12) yields a certificate with the same end and pattern $q$, with parameters

$$
\boxed{g^{\,2^m}(m).}
\tag{15}
$$

The entire proof uses the explicit $2^m$ for finite induction, without seeking to normalize the length of some unbounded M. The formula (15) magnifies the parameters, not the number of rows in the BMS.

## Finite certificate of standard root

Starting from the standard notation $P_{\rm start}$, with the parameter 1. Writing $M$ indicates that this directory is fixed at $M_\star$, and writing $E$ indicates $E(1)$. The following 32 steps maintain the parameters 1 and the original end:

    M M M E M M M M
    E E E M M E E E
    M M E E E E M M
    E E E M M E E E

The obtained $P$ has 36 rows. The last four are core, step size, and marks.

$$
\begin{array}{c|c|c|c}
r&A_r&L_r&\text{marks}\\ \hline
33&(0,1,2,3,33)&2&\{3\}\\
34&(0,1,2,33,34)&3&\varnothing\\
35&(0,1,2,3,35)&2&\{3\}\\
36&(0,1,2,3,36)&2&\{3\}.
\end{array}
\tag{16}
$$

First, relocate the last two long lines. Change the parameters from 1 to 2, then to 8, leaving the 34 line. For the new last two lines, use (15) to obtain a fixed pattern $Q$ with only 32 lines, but with parameters.

$$
\boxed{B=g^{256}(8)=g^{258}(1).}
\tag{17}
$$

The end is always the initial $\Theta_0<\kappa_4$, and the first two bases are always fixed. The specific literal pattern of $Q$ is the 32th row of $P$; it still only contains rows whose step size does not exceed 4. This last point indicates that (17) is never equal to the BMS that has already obtained the $B$ row.

A finite certificate program (historical reference: `prefix_rebase_probe.py`) compares the above 32 step results with the literal patterns written independently for the 36 lines, and then checks the $E(8)$ exact generation of 256 lines of (14) long lines. It completes 292 structural audits, checking regular lines, Sat, PosSource, exact traces, and mark recovery; without assuming the internal adjacency lines that are not necessary in nature. The 2026-10-14 operation is completed in approximately 0.08 seconds, retaining at most 288 lines. There is never numerical expansion in $B$.

This mathematical research paper aims to provide a proof for program verification of finite grammar computations. The meaning of relocation in embedding is provided by the proof of (4)—(9), and this cannot be reversed to use the program to replace this mathematical proof.

## After zooming in, switch to the unmarked rule

Removing all marks from any $\mathcal C$ certificate immediately results in a ordinary BLS, while parameters such as embedding, cardinality, endpoint, and linedness remain unchanged. Therefore, after reaching $Q,B$, marking completion can be completely stopped, and the ordinary BLP $M/E$ and quantitative theorem can be used instead.

$$
\Theta_0\ge
\gamma_{\,2^{\,f(\operatorname{forget}Q,B)}}.
\tag{18}
$$

Since within the same generating algebra, $\Theta_0<\kappa_4=\gamma_{F(4)}$ and $q(5)=F(4)+1$ are strictly equivalent

$$
\boxed{q(5)>2^{\,f(\operatorname{forget}Q,B)}.}
\tag{19}
$$

The formula (19) defines a well-defined mixed-phase numerical lower bound, but it has not been compared with the existing $2^{f_\star(P_{\rm start},1)}$ or the three-row BMS descent number bounds. Therefore, it cannot be considered the strongest numerical bound at present. In particular, it has not been proven to exceed the specified BMS[10] rapid growth value.

If the ordinary native completion is also to be discontinued in the subsequent stage, it is necessary to create a true BMS with no completions. Only removing the marks ensures the ordinary BLP implementation, but it does not guarantee that the subsequent native packages will be empty.

## The next structural conclusion required

There is now a real low-end point entrance: the fixed $Q$ has a vast range of available parameters, $B$, rather than raising the endpoint to a much higher value, $\kappa_r$, for larger parameters. In the future, we can try parameters with $E(B)$, completions with a definite number of steps, or even stronger prefix relocation methods (10).

However, it must be continued to prove that: the structure produced by these operations supports **Compatible multi-row BMS mapping**, and the initial endpoints remain within the same bounds. The large number of cloned rows, the large step size of a certain row, and the large linedness parameter cannot alone replace this conclusion. The previous finite window counterexamples (historical reference: `copy-budget-obstructions.zh-CN.md`) have also ruled out the direct inference that "ordinary linedness automatically provides any length compatible window."

This research focus has shifted to a lemma on parameterized structure magnification, rather than manually searching for the fourth and fifth layers. Ten layers are just the target baseline; if the unified transfer of parameters to the number of layers holds, then the scale of (17) can be utilized at once. This unified transfer, as well as the comparison to the fixed BMS rapid growth value, still needs to be proven.
