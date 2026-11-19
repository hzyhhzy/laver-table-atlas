# Sharing the 012 port provides a larger q(5) initialization · [中文版](active-port-stronger-initialization.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper, within the framework of ZFC + I3, with actual certificates for the same `Iter(j)`, and finite parameter quantitative bridges for parent packages, strictly improves the lower bound for pure integers in `G(1)=f_PP(S,1)`. It does not compile any complete super-BMS ordinal notations into pIBLP, nor does it directly treat the full index ordinal type as a finite parameter for recursive growth.

Let `F=P4=S[0]^5`, `P5=S[0]^4`, and denote

$$
H(m)=f_{\rm PP}(F,m),\qquad C=H(1),\qquad B=H(C).
$$

Already have [Pure E reduction](<../piblp-external-FGH-20261014/P4-pure-E-collapse.md>), please correctly write `H` as `u_(ω^ω)`. This article only requires that the `H(1)=C` and all actually used calls meet the `H(m)≥m2^m` criteria. It does not require global input monotonicity.

New conclusion:

$$
\boxed{G(1)\ge H^{\circ(2^B+2)}(1).}
\tag{1}
$$

The old initialization only uses `G(1)≥H²(1)=B`. The formula (1) follows the same strictly increasing `H` trajectory, using an exponential number of iterations with `B`, thus being strictly increasing.

## 1 A correct finite-parameter entry point, not just a NER reachable path

Following the ascending order of core, abbreviations for the step length after colons:

```text
F  = 01:1 012:1 0123:2 012*34:2
P5 = F 01235:3
```

The "mark" in the fourth line is the address 3. The asterisk is used only to indicate the mark, not as an additional core element. With the parameter 1, `P5` is equivalent to E-limit, hence `f(P5,1)=f(E_P5(1),1)`. The complete result of one true auxiliary E and one ordinary short M is...

```text
E_P5(1)   = F 0125:2 012*56:2
M(E_P5(1))= F 0125:2 256:1 2567:2 256*78:2 .
```

These two lines are both "transient" (not marked as E-successor or E-limit), and the entire "guard" has been fully replicated for the first time. The latter item has a prefix.

```text
T = F 0125:2 256:1 .
```

Perform a M operation on T, and the result and its prefix V are

```text
M(T) = F 0125:2 01256:3 0125*67:3
V    = F 0125:2 01256:3 .
```

The guard for T has passed, and the last line is transient, so it is `f(T,1)=f(M(T),1)`. V is then E-limit, the root address is 5, and its auxiliary E(1) only copies the 5th line at the end, resulting in

```text
E_V(1) = F 0125:2 0126:2 .
```

This step does not scan the parent package; the rows with F and the marks remain unchanged. V is precisely the active graft of 0, 1, and 2, `F⋉p_ω`. However, these finite arrays are sufficient to prove the functional equations mentioned later, and it is not necessary to assume a general active graft with full index simulation.

## 2 actually refers to semantics, definiteness, and cap.

P5 is the actual prefix of S, retaining the same first three points and the initial 1-linedness. The parent package quantitative bridge supply E and M have true implementations and all natural truncation mark certificates; their cap does not exceed S's `θ6<κ4`. The prefix implementations of T and V also inherit the same first three points.

The two M used in the above path are indeed f recursive transient branches, and not arbitrary substitutions of NER `[2]` for some E branches. Each time a prefix is taken, only the proven lemma "within the same actual realization, the prefix values remain constant under fixed parameters" is applied.

$$
\begin{aligned}
G(1)&\ge f(P5,1)=f(E_{P5}(1),1)\\
&=f(M(E_{P5}(1)),1)\ge f(T,1)\\
&=f(M(T),1)\ge f(V,1).
\end{aligned}
\tag{2}
$$

All these calls and the subsequent definitional calls with large parameters that result in E-successor are given by the same finite table potential induction and the dual block quantitative bridge. There is no assumption that the fixed original triple can support any large parameter, nor is it assumed that G is globally finite.

## 3 Two E-successor exactly generate a large number of H iterations

Let R=F be followed by a global `012n:2` on the E-successor row, and denote it as

$$
K(m)=f(R,m)=H^{\circ 2^m}(m).
\tag{3}
$$

The one auxiliary E(1) that results from V exactly gives F followed by two such E-successor lines. Therefore,

$$
f(V,1)=K^{\circ2}(1)=K(B)
=H^{\circ2^B}(B)=H^{\circ(2^B+2)}(1).
\tag{4}
$$

Here, `K(1)=H²(1)=B`, each equation is an exact equality defined by the original recursion. Combining with (2), we obtain (1). In particular, there is no need to infer "more computation" from "a larger ordinal type".

## 4 returns to the existing BMS feedback.

Let

$$
J=H^{\circ(2^B+1)}(1),\qquad
\rho(x)=x+3+\lceil\log_2(x+2)\rceil .
$$

From (1) and the general lower bound `H(J)≥J2^J`, the new actual height `h*=G(1)+2` is satisfied

$$
h_*\ge J2^J+2\ge\rho(2^J),
\tag{5}
$$

The last step is only written as `J≥3`: `ρ(2^J)=2^J+J+4≤J2^J+2`. The actual front-end insertion, endpoint templates, and FGH buffer compilation are exactly the same as in the [There is an enhancement of the lower bound.](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.md>) section, 3–5 section.

$$
\boxed{q(5)>F_{\Lambda+\omega}
 \bigl(F_\Lambda(F_\Lambda(2^J))\bigr),\quad
\Lambda=\lim(\mathrm{BMS}).}
\tag{6}
$$

We still agree to use `(Λ+ω)[x]=Λ+(x+1)`. This right-hand side strictly exceeds the original `2^C` input's right-hand side: along the same H trajectory, there is `J>C`, and the strictly monotonicity of the BMS diagonal input, which has been proven separately, is sufficient. This does not rely on the general FGH subscript monotonicity. If a more concise but weaker expression is needed, it can be changed to

$$
J_0=H^{\circ C}(1)
$$

Instead of J, because `2^B+1≥C`, there is `J≥J0` along the same H trajectory.

This advancement enhances the actual numerical initialization, but the main FGH subscripts remain `Λ+ω`. It cannot answer the question of "sending Y, RPD, or another complete hyper-BMS system into pIBLP."

## 5 A finite array of certificates

active-port-initialization-audit.py (Historical reference: `active-port-initialization-audit.py`) Gradually checks the complete core, steps, and marks of the aforementioned E, M, T, V, and examines each guard. The clear upper limit is two seconds, 30 rows, and 1000 storage items; the actual 9 rows, 46 storage items, with a single round being insufficient to exceed 0.1 seconds. It does not calculate the decimal values of any large iterations, nor does it have any background processes.

The general `[1]` in NER is first-item, and `[2]` is a short M. However, for the specific item P4, the complete sets of both are exactly the same, and the certificates also assert this fact. Therefore, the old manuscript's name A does not lead to any actual difference in this case. This paper directly describes the complete forms of T and V.

## The macro that takes 6 two steps will increase the control that is purely E to omega to the power of omega.

It can also not stop at the prefix V of M(T), but perform a transient M on M(T) again. The seven-line prefix of the resulting term is

```text
Q = F 0125:2 01256:3 567:1 .
```

The Q has passed the guard, and the last line is also transient. A short M just happens to be sufficient.

```text
Z = M(Q) = F 0125:2 01256:3 01267:3 = F⋉p_(ω^ω) .
```

Therefore, the comparison of prefix values is as `G(1)≥f(Z,1)`. For any basis function H, the recursion of [Theorem of Function Substitution for Shared Ports](<../piblp-external-FGH-20261014/active-E-graft-functional-substitution.md>) is continued.

$$
U_0^H=H,\qquad U_{\alpha+1}^H(m)=(U_\alpha^H)^{\circ2^m}(m),\qquad
U_\lambda^H(m)=U_{\lambda[2^m]}^H(m),
$$

Obtaining a stronger exact bound

$$
\boxed{G(1)\ge U_{\omega^\omega}^H(1).}
\tag{7}
$$

H itself is already `u_(ω^ω)`, so to be precise, the right side is `u_(ω^ω·2)(1)`: For the fixed β=ω^ω and α≤ω^ω here, `u_(β+α)=U_α^(u_β)` can be generalized by α, because the basic sequences used exactly satisfy `(β+α)[n]=β+α[n]`, and the successors are also compatible. Here, `ω^ω·2` is still just a control subscript with finite parameters, not the order type of the entire pIBLP.

In order to send back (7) to the buffered BMS initialization, let

$$
\widehat J=U_{\omega+1}^H(1).
$$

At the parameter 1, the third-order derivatives are successively `ω^ω→ω²→ω·2→ω+2`. Therefore

$$
U_{\omega^\omega}^H(1)
=U_{\omega+2}^H(1)
=(U_{\omega+1}^H)^{\circ2}(1)
=U_{\omega+1}^H(\widehat J)\ge H(\widehat J)
\ge\widehat J2^{\widehat J}.
\tag{8}
$$

Among them, `U_α^H(m)≥H(m)` can be directly inferred from α: the first round of the subsequent iteration already satisfies this bound, and subsequent rounds only need to use `U_α^H(x)≥x`, without the need for H to ensure monotonicity of the input. The limit is inherited downward. All calls in this instance can also be directly defined by the quantitative bridges of the actual Z.

Therefore, the previous J can be further improved to `Ĵ`, and there is

$$
\boxed{q(5)>F_{\Lambda+\omega}
 \bigl(F_\Lambda(F_\Lambda(2^{\widehat J}))\bigr).}
\tag{9}
$$

This strictly enhances (6):`Ĵ=(U_ω^H)²(1)>U_ω^H(1)>J`), which are finite comparisons on the same value increment track. The monotonicity of the BMS input is proven. If combined with [Dynamic Depth Template](<dynamic-depth-Lambda-omega-successor.md>), then `x=2^Ĵ` can also be used to achieve the same result.

$$
q(5)>F_{\Lambda+\omega+1}
 \!\left(F_{\Lambda+\omega}(F_\Lambda(F_\Lambda(2^{\widehat J})))\right).
\tag{10}
$$

All new arrays have been assigned the same bounded certificate. The strict comparison of the formula (7)—(10) comes from the aforementioned recursive equations and actual implementations, and is not a universal embedding inferred from a limited number of examples.
