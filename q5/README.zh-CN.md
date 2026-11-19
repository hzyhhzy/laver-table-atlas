# 不用 I3 的周期 32 下界 · [English](README.md)

**只要 $q(5)$ 存在，就有 $q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3)$。** 定理还有一个可以直接读成表项的版本。以 $A_m$ 表示有 $2^m$ 个元素的普通二元 Laver 表，元素按模 $2^m$ 的余数编号，则

$$
 A_m(1,16)\ne 0
 \quad\Longrightarrow\quad
 F_{\lim(\mathrm{BMS})+\omega+1}(3)
 \text{ 的求值终止，且其值小于 }m .
$$

因此在任何已有 $A_m(1,16)\ne0$ 的阶上都能应用这个定理。取第一个这样的 $m$，就是首页的 $q(5)$。[有限周期与首次达到的定义](../laver_table_lower_bounds/lean/LaverLowerBounds/FinitePeriods.lean) · [最终定理](../laver_table_lower_bounds/lean/LaverLowerBounds/OriginalBMSBound.lean)

## 为什么看第 16 列？

首行的周期是 2 的幂，行在一个周期的末尾取零。在阶数增加时，周期保持或翻倍。因此第 16 列非零等价于首行的周期至少为 32。首次达到这一条件时，周期恰为 32。[周期引理](../laver_table_lower_bounds/lean/LaverLowerBounds/FinitePeriods.lean)

## 右边是哪一个数？

$F$ 是 FGH（fast-growing hierarchy，快速增长层级），$\lim(\mathrm{BMS})$ 是 BMS（Bashicu matrix system）的极限。这里取 $F_0(x)=x+1$，后继层级将前一层函数迭代 $x+1$ 次，极限层级取基本列第 $x$ 项。$\lim(\mathrm{BMS})$ 的第 $x$ 项取 $x+1$ 行的两列种子，第一列全零，第二列全一。再上一段取 $(\lim(\mathrm{BMS})+\omega)[x]=\lim(\mathrm{BMS})+(x+1)$。这些约定决定了定理右边的具体值。[BM4 展开规则](../laver_table_lower_bounds/lean/YesMetaZFC/BMS/Reference.lean) · [层级和求值关系](../laver_table_lower_bounds/lean/LaverLowerBounds/NumericFGH.lean)

Lean 的结论是存在一个自然数 $y$，有一棵依照上述规则算出 $y$ 的有限求值树，且 $y<m$。证明先在 BMS 的父表坐标中从周期条件取得这棵树和严格上界，再利用逐步展开的等价性，将求值换回原数值 BM4。求值的唯一性保证所有这样的树算出同一个 $y$。整个推导只用普通有限表族的定义方程及周期假设。[有限表中的求值与上界](../laver_table_lower_bounds/lean/LaverLowerBounds/FiniteFGHBound.lean) · [两种坐标的求值等价](../laver_table_lower_bounds/lean/LaverLowerBounds/NumericFGH.lean)

该结果在 Lean 4.33.1 的通常基础下核验。最终三个定理的传递公理清单均为 `propext`、`Classical.choice` 和 `Quot.sound`。周期阈值的存在是首页命题的前提。迁入本图谱后，重新编译了全部 152 个模块，统一换行后的编译日志与原记录逐字相同。[源码与公理清单](../laver_table_lower_bounds/lean/verification/VERIFICATION.json) · [完整日志](../laver_table_lower_bounds/lean/verification/build.txt) · [重建方法](../laver_table_lower_bounds/lean/README.zh-CN.md)

[返回首页](../README.zh-CN.md)
