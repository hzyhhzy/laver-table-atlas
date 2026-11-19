# pIBLP initial long chains strictly exceed the original literature constant · [中文版](audit-piblp-strict-Cline.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Under the actual realization conditions of [pIBLP finite parameter quantitative bridge](<../iblp-030-laver-20261014/parent-packet-quantitative-transfer.md>) and ZFC + I3, denote as

$$
G(m)=f_{\rm PP}(S,m),\qquad
H(m)=f_{\rm PP}(P_4,m),\qquad C=C_{\rm line}=H(1),
$$

Among them, $S$ are the nine actual seeds, and $P_i$ are the first $i$ lines before them.

$$
\boxed{G(1)\ge H(C)\ge C2^C>C.}\tag{1}
$$

All the partially recursive calls used here are defined for the actual finite potential induction; it is not assumed that $G,H$ is fully defined for all parameters, nor is it assumed that they are monotonic with respect to the parameters.

## A primary auxiliary copy and a prefix

Using a basis to show, core inverse order. The two prefixes are

```text
P4 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2
P5 = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,3,2,1,0)3
```

The end core of $P_5$ is ordered as $(0,1,2,3,5)$, with a step size of 3, thus it is E-limit. Its complete copy passes the guard test, and the recursive branch with the finite parameter 1 is given.

$$
f_{\rm PP}(P_5,1)=f_{\rm PP}(E_{P_5}(1),1).\tag{2}
$$

The auxiliary rules are as follows: first take $\operatorname{cut}P_5=P_4$, add a line of $(3,5):1$, then perform a raw short copy operation; this operation does not scan native or marks. The original line has a step length of 1, the control point is $a=3$, the source lines are the 3 and 4 lines, and the address translation is $\psi_3(x)=x$$x<3$ and $x+2$$x\ge3$. The short copy operation turns the 3 line into the core $(0,1,2,5):2$, and turns the 4 line and its mark into $(0,1,2,*5,6):2$. So the complete result is

```text
E_P5(1) = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,2,1,0)2(6,*5,2,1,0)2
```

It has five characters in front of the prefix.

```text
R = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,2,1,0)2
```

The end core of $R$ is $(0,1,2,5)$, the step size is 2, the marks are empty, and the complete copy of the guard also passes. Therefore, $R$ is E-successor, and also $\operatorname{cut}R=P_4$.

## Strict numerical increment

[Monotonicity of prefix values within the same actual BLS](<baseline-piblp-Cline-prefix.en.md>) are used for $P_5\sqsubseteq S$ and $R\sqsubseteq E_{P_5}(1)$ under the fixed current parameter 1, respectively.

$$
G(1)\ge f_{\rm PP}(P_5,1)
=f_{\rm PP}(E_{P_5}(1),1)
\ge f_{\rm PP}(R,1).
$$

The definition of E-successor iterates exactly twice, therefore

$$
f_{\rm PP}(R,1)
=H^{\circ2}(1)=H(H(1))=H(C).\tag{3}
$$

The definitiveness of the two sub-calls of this equality is given by the inductive construction of the E-successor double block with quantitative bridges. The prefix implementation retains the same current finite parameters as the original three points, without additional requirements for common linedness on any parameters. The small pattern derivation gives $H(1)=C$. A general lower bound for the finite evaluation tree is provided.

$$
f_{\rm PP}(P,m)\ge m2^m
$$

Applying the currently defined $H(C)$ yields (1). This represents a strict increase in the actual recursive value, not a decrease in length inferred from the ordinal increase.

## Larger valid entrance height

The $G(1)$-lined $(\kappa_0,\kappa_1,\theta_6)$ output an overall $E=L_3(K)$-image, resulting in a $G(1)$-lined $(\kappa_2,\theta_6,\tau)$ chain. The unified front insertion gives a certain height.

$$
h_*=G(1)+2
$$

The legal entrance fan has a closure strictly less than $\tau$. Therefore, the recursive corridor endpoint theorem and [FGH strong buffer compilation](<audit-recursive-corridor-FGH.md>) can be applied to this height. From $C\ge3$, let $x=2^C$, there is

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil=2^C+C+4
\le C2^C+2\le h_*.
$$

Therefore, the same compilation proof directly provides another clear bound.

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(F_\Lambda(F_\Lambda(2^C))\bigr).}\tag{4}
$$

Here, we still agree to use $(\Lambda+\omega)[x]=\Lambda+(x+1)$. The value of $2^C>F_3(256)$ cannot be derived without proving the monotonicity of $F_\Lambda$. Specifically, the right-hand side of (4) is strictly greater than the right-hand side of the old bound. The necessary special comparison has now been filled in by [BMS Diagonal Input Monotonicity](<audit-BMS-diagonal-input-monotonicity.md>): It uses the prefix of the fundamental sequence and the number of rows of the two seed columns to compare, without assuming any general monotonicity of FGH subscripts. Therefore, the right-hand side of (4) is indeed strictly greater than
$F_{\Lambda+\omega}(F_\Lambda(F_\Lambda(F_3(256))))$.
The integrated conclusions are provided in [pIBLP enhances the lower bound.](<q5-piblp-enhanced-bound.md>).

## Finite verification

audit-P5-strict-prefix.py (Historical reference: `audit-P5-strict-prefix.py`) Independently constructs and asserts for each item the $P_5$ raw auxiliary replication, all steps and marks, the $R$ type of E-successor lines and guards, as well as the $\operatorname{cut}R=P_4$. It has a budget of two seconds, 20 lines, and 500 storage items. It does not evaluate any large recursive values; the universal numerical deduction is given by the comparison argument of the finite potential and prefixes above.
