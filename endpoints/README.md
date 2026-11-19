# From period 32 to smaller critical points · [中文版](README.zh-CN.md)

Fix an I3 embedding $j$. Write $J_1=j$, $J_{a+1}=J_a(j)$ and $\kappa_i=j^i(\operatorname{crit}j)$. Parentheses between embeddings denote application, and parentheses around an ordinal denote its image. Enumerating the generated critical points from $\gamma_0$ gives $\kappa_2=\gamma_2$, $\kappa_3=\gamma_4$ and $\kappa_4=\gamma_{q(5)-1}$. If $J_a(\gamma_t)=\gamma_s$, the table of order $m$ reads off $\min(s,m)$ as the 2-adic valuation of $A_m(a,2^t)$, with valuation $m$ assigned to zero. [Conventions](../laver_table_lower_bounds/common/conventions.md) · [Finite-table equalities](../laver_table_lower_bounds/lean/LaverLowerBounds/LowConstants.lean)

## The upper part of the chain

Put $\mu=J_7(\kappa_2)=\gamma_{256}$. The strict comparisons are

$$
\begin{aligned}
\kappa_4&>J_5(\kappa_2)>J_7(\mu)>J_7(\kappa_3)>J_9(\kappa_3),\\
J_9(\kappa_3)&>J_{11}\bigl(J_{11}(\kappa_3)\bigr)>J_{10}(\kappa_3)>J_{11}(\kappa_3).
\end{aligned}
$$

For the first line, $J_5(\gamma_3)=\kappa_4$ and $\kappa_2<\gamma_3$. The finite-table estimate for double application gives $J_7(\mu)<J_5(\kappa_2)$. The remaining comparisons on that line follow from $\kappa_3<\mu$, $J_8(\gamma_8)=J_9(\kappa_3)$ and $J_8(\mu)=J_7(\kappa_3)$. The three strict comparisons on the second line are the finite-table Lean lemmas `seven_lt_eight`, `six_lt_seven` and `five_lt_six`. [Double application and images](../laver_table_lower_bounds/lean/LaverLowerBounds/CappedAlgebra.lean) · [Upper endpoint data](../laver_table_lower_bounds/lean/LaverLowerBounds/HigherConstants.lean)

## The lower part of the chain

Put $b=(J_{11}(J_3))(J_7)$ and $e=b(j)$. Then

$$
J_{11}(\kappa_3)>J_{13}(\gamma_{16})>b(\kappa_3)>b(\gamma_3)>b(\kappa_2).
$$

Equation (4) in the common endpoint proof gives the first inequality. Equation (8) first compares the remaining images for a local term $b_0$. The terms $b_0$ and $b$ agree at the cutoff $J_{13}(\gamma_{16})$. All three outputs lie strictly below that cutoff, so each can be read as an image under $b$. [Common endpoint proof, equations (4), (6), (8) and (9)](../laver_table_lower_bounds/lower_endpoints/endpoints.md)

| Endpoint | Bound or exact value |
|---|---|
| $b(\gamma_3)=\gamma_s$ | $s>F_C(6)$, where $C=\varepsilon_{\lim(\mathrm{BMS})+1}$. [BMS tower proof](../laver_table_lower_bounds/lower_endpoints/bms.md) |
| $b(\kappa_2)=\gamma_r$ | A 25-row ordinary BLP gives $r\ge2^{f(P_{25},8)}$. The same endpoint also realizes a specified marked version. [Proof](../laver_table_lower_bounds/lower_endpoints/blp.md) |
| $e(\gamma_{1024})=\gamma_{v_3}$ | The seven-row $p_{\rm init}$ gives $v_3\ge2^{f(p_{\rm init},8)}$. [Section 5](lower-blp-points.md) |
| $e(\gamma_{513})=\gamma_{v_2}$ | A four-row pattern gives $v_2\ge m_{\omega+2}(2)$ for the Steinhaus–Moser hierarchy used in the proof. [Section 5](lower-blp-points.md) |
| $e(\gamma_{512})=\gamma_{v_1}$ | A three-row pattern gives $v_1>2\uparrow\uparrow259$. [Section 4](lower-blp-points.md) |
| $J_{11}(\gamma_3)$ | Exactly $\gamma_{2^{2048}}$. [Paper proof and Lean theorem](../exact-values/j11-gamma3/README.md) |

In the first row, $\lim(\mathrm{BMS})$ is a fixed point of $\alpha\mapsto\varepsilon_\alpha$, and $C$ is the next epsilon number. Its FGH uses the fundamental sequences of the tower proof. [Tower ranks and fundamental sequences](../laver_table_lower_bounds/01-blp-tower.md)

The six endpoints in the left column decrease strictly. The right column gives the bound established separately at each endpoint. Comparing any two of those numerical estimates requires a numerical comparison of its own. Lean certifies several endpoint comparisons and independently gives a $\lim(\mathrm{BMS})+1$ bound when row 11, column 16 is nonzero. [Scope of the finite-table formalization](../laver_table_lower_bounds/lower_endpoint_lean/README.md)

[Supporting calculations](notes/README.md)

[Back to the atlas](../README.md)
