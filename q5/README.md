# A period-32 bound without I3 · [中文版](README.zh-CN.md)

**If $q(5)$ exists, then $q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3)$.** There is also a version for a single entry of any ordinary binary Laver table $A_m$. Number its $2^m$ elements by residues modulo $2^m$. Then

$$
A_m(1,16)\ne0\quad\Longrightarrow\quad
F_{\lim(\mathrm{BMS})+\omega+1}(3)\text{ has a finite evaluation with value less than }m.
$$

The statement applies at every order where the entry is nonzero. The first such order is $q(5)$. [Finite periods and the threshold](../laver_table_lower_bounds/lean/LaverLowerBounds/FinitePeriods.lean) · [Final Lean theorem](../laver_table_lower_bounds/lean/LaverLowerBounds/OriginalBMSBound.lean)

## Why column 16?

The first row has period a power of two. Its zeros occur exactly at multiples of the period. On passing to the next order the period stays the same or doubles. Thus the entry in column 16 is nonzero exactly when the period is at least 32, and at the first such order the period is exactly 32. [Period lemmas](../laver_table_lower_bounds/lean/LaverLowerBounds/FinitePeriods.lean)

## Which FGH value?

$F$ denotes the FGH (fast-growing hierarchy), and $\lim(\mathrm{BMS})$ is the limit of the Bashicu matrix system. We take $F_0(x)=x+1$, iterate the preceding function $x+1$ times at a successor, and take entry $x$ of the fundamental sequence at a limit. Entry $x$ at the BMS limit is the two-column seed with $x+1$ rows, a zero first column and an all-ones second column. The next limit used here has $(\lim(\mathrm{BMS})+\omega)[x]=\lim(\mathrm{BMS})+(x+1)$. These choices fix the numerical bound. [BM4 expansion](../laver_table_lower_bounds/lean/YesMetaZFC/BMS/Reference.lean) · [FGH evaluation](../laver_table_lower_bounds/lean/LaverLowerBounds/NumericFGH.lean)

Lean produces a natural number $y$ and a finite evaluation tree for it, with $y<m$. The proof obtains the tree and the strict bound in BMS parent coordinates from the period hypothesis. Stepwise equivalence of the expansions then transports the evaluation to the original numerical BM4 rule. Uniqueness shows that every such tree gives the same $y$. The argument uses the defining equations of the finite-table family and the stated period hypothesis. [The finite-table bound](../laver_table_lower_bounds/lean/LaverLowerBounds/FiniteFGHBound.lean) · [Equivalence of the evaluations](../laver_table_lower_bounds/lean/LaverLowerBounds/NumericFGH.lean)

All 152 modules were rebuilt in Lean 4.33.1 in the Atlas directory. The resulting log agrees with the original after newline normalization. The three final theorems use only `propext`, `Classical.choice` and `Quot.sound`. [Verification record](../laver_table_lower_bounds/lean/verification/VERIFICATION.json) · [Build log](../laver_table_lower_bounds/lean/verification/build.txt) · [Rebuild instructions](../laver_table_lower_bounds/lean/README.md)

[Back to the atlas](../README.md)
