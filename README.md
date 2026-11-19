# Laver Table Atlas · [中文版](README.zh-CN.md)

The results presented in this repository were obtained by GPT Astra.

## Results at a glance

- **Lower bounds in Laver tables**

  - If $q(5)$ exists, then **$q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3)$**. [Finite-table proof in Lean](q5/README.md)
  - Under I3, writing $J_{13}(\gamma_{16})=\gamma_N$, we have $q(5)>N>F_{\varepsilon_{\lim(\mathrm{BMS})+1}}(6)$. [BMS tower and endpoint comparisons](endpoints/README.md)
  - Under I3, the 25-row BLP $P_{25}$ is realized below $J_{13}(\gamma_{16})$, giving $q(5)>2^{f(P_{25},8)}$. [25-row BLP proof](laver_table_lower_bounds/lower_endpoints/blp.md)
  - Whenever row 11, column 16 is nonzero, its 2-adic valuation exceeds $F_{\lim(\mathrm{BMS})+1}(120)$. [Finite-table theorem in Lean](laver_table_lower_bounds/lower_endpoint_lean/README.md)

- **Exact values in Laver tables**

  - Under I3, $J_{11}(\gamma_3)=\gamma_{2^{2048}}$. [Exact value and proof](exact-values/j11-gamma3/README.md)

- **$BB(27)>q(5)$**

  - If $q(5)$ exists, this 27-state machine starts on a blank tape and halts with exactly $2^{q(5)}+3$ ones. [Machine and proof](busy-beaver/q5-27/README.md)

## At what order does the first row reach period 32?

**If $q(5)$ exists, then**

$$
\boxed{\displaystyle q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3).}
$$

**Lean-checked, without I3.** Here $q(5)$ is the first order at which the first row of an ordinary binary Laver table reaches period 32. The table of order $m$ has $2^m$ elements. The function $F$ denotes the FGH (fast-growing hierarchy), and $\lim(\mathrm{BMS})$ is the limit of BMS (Bashicu matrix system). We chose this very weak bound for ease of formalization. Stronger bounds proved under I3 appear below. [Final theorem](laver_table_lower_bounds/lean/LaverLowerBounds/OriginalBMSBound.lean) · [Conventions and verification](laver_table_lower_bounds/lean/README.md)

## BMS gives an extremely loose lower bound for $q(5)$. Long before the first row reaches period 32, $J_{13}(\gamma_{16})$ already supports growth far beyond BMS.

Enumerate the generated critical points in increasing order as $\gamma_0,\gamma_1,\ldots$ and write $J_a$ for the $a$-th left power of $j$. Put $J_{13}(\gamma_{16})=\gamma_N$. In ZFC + I3,

$$
\boxed{\displaystyle q(5)>N>F_C(6),\qquad C=\varepsilon_{\lim(\mathrm{BMS})+1}.}
$$

Since $\varepsilon_{\lim(\mathrm{BMS})}=\lim(\mathrm{BMS})$, $C$ is the first epsilon number above the BMS limit. The function $F_C$ uses the fundamental sequences of the tower proof. The endpoint realizing this bound lies lower still, at $b(\gamma_3)$ where $b=(J_{11}(J_3))(J_7)$. [FGH bound](laver_table_lower_bounds/lower_endpoints/bms.md)

Let $\kappa_i$ be the critical sequence of $j$, with **$\kappa_2=\gamma_2$ and $\kappa_3=\gamma_4$**. Starting at the critical point for $q(5)$ gives the chain

$$
\begin{aligned}
\gamma_{q(5)-1}=\kappa_4
 &>J_5(\kappa_2)>J_7(\gamma_{256})>J_7(\kappa_3)\\
 &>J_9(\kappa_3)>J_{11}\bigl(J_{11}(\kappa_3)\bigr)>J_{10}(\kappa_3)\\
 &>J_{11}(\kappa_3)>J_{13}(\gamma_{16})\\
 &>b(\kappa_3)>b(\gamma_3)>\gamma_{F_C(6)} .
\end{aligned}
$$

The full chain with its FGH bound is a paper result in ZFC + I3. Several comparisons in its upper part also have finite-table Lean proofs. [Proof of the smaller endpoints](laver_table_lower_bounds/lower_endpoints/endpoints.md) · [Bound at the last endpoint](laver_table_lower_bounds/lower_endpoints/bms.md)

### The BLP lower bound

Put $e=b(j)$. Below $b(\gamma_3)$ there is a second chain of realized basic Laver patterns.

$$
\begin{aligned}
b(\gamma_3)
 &>\underbrace{b(\kappa_2)}_{25\text{ rows}}
  >\underbrace{e(\gamma_{1024})}_{7\text{ rows}}
  >\underbrace{e(\gamma_{513})}_{4\text{ rows}}\\
 &>\underbrace{e(\gamma_{512})}_{3\text{ rows}}
  >J_{11}(\gamma_3)=\gamma_{2^{2048}} .
\end{aligned}
$$

The index of the 25-row endpoint is at least $2^{f(P_{25},8)}$ for the ordinary BLP recursion, including completion. We conjecture that completion can make BLP grow far faster than BMS. Comparing these numerical bounds requires an estimate of how much the new rows contribute through later copies and modifications. [25-row BLP proof](laver_table_lower_bounds/lower_endpoints/blp.md) · [Smaller patterns](endpoints/lower-blp-points.md)

## An exact value in row 11, column 8

Under I3, $\displaystyle J_{11}(\gamma_3)=\gamma_{2^{2048}}$. Writing $11_{2.5}$ for this point's index gives $11_{2.5}=2^{2048}$. With the residue convention modulo $2^m$, **row 11, column 8 first becomes nonzero at order $2^{2048}+1$**. The equality has been verified in Lean. [Paper proof](exact-values/j11-gamma3/proof.md) · [Lean theorem](exact-values/j11-gamma3/lean/RankSteelEndpoint.lean)

## A 27-state machine writes the table width on a blank tape

This binary machine halts exactly when $q(5)$ exists. At halt it leaves exactly $2^{q(5)}+3$ ones. Write $\Sigma(27)$ for the maximum number of ones left at halt and $BB(27)$ for the maximum runtime. Each step increases the number of ones by at most one, so a machine starting on a blank tape takes at least as many steps as it leaves ones. Whenever $q(5)$ exists,

$$
BB(27)\ \ge\ \Sigma(27)\ \ge\ 2^{q(5)}+3\ >\ q(5).
$$

In ZFC + I3 the first-row periods are unbounded, so the machine halts. [Construction and verification](busy-beaver/q5-27/README.md) · [54 numerical transitions](busy-beaver/q5-27/transitions.txt) · [Machine file](busy-beaver/q5-27/machine.tm)

## Related results

- **Row 11, column 16.** If this entry is nonzero at order $m$, then $F_{\lim(\mathrm{BMS})+1}(120)<v_2(A_m(11,16))<m$. [Finite-table Lean theorem](laver_table_lower_bounds/lower_endpoint_lean/README.md)
- **Larger inputs and supporting lemmas.** The paper proofs also cover large inputs at level $\lim(\mathrm{BMS})+\omega+1$ and lower bounds on the number of fixed-index BMS expansions. [Dynamic BMS proof](laver_table_lower_bounds/02-bms-feedback.md) · [Fixed-index lemma](laver_table_lower_bounds/common/bms-fixed-index.md)

The lower-bound papers and original Lean projects come from one revision of the ordinal-notations repository. The Atlas includes English and Chinese editions of the papers, the smaller-endpoint PDFs and the supporting notes. [Collection index](laver_table_lower_bounds/README.md) · [Smaller-endpoint PDFs](laver_table_lower_bounds/lower_endpoints/README.md) · [Source revision](https://github.com/hzyhhzy/column-ordinal-notations-hzy/tree/dd652aea4ac52d901b22eeff83b4196f9e5f6312/laver_table_lower_bounds)
