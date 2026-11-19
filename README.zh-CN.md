# Laver 表图谱 · [English](README.md)

本仓库的各个结果由 GPT Astra 完成。

## 主要结果

- **Laver 表的下界**

  - 只要 $q(5)$ 存在，就有 **$q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3)$**。[有限表证明（Lean）](q5/README.zh-CN.md)
  - 在 I3 下，写 $J_{13}(\gamma_{16})=\gamma_N$，则 $q(5)>N>F_{\varepsilon_{\lim(\mathrm{BMS})+1}}(6)$。[BMS 指数塔与端点比较](endpoints/README.zh-CN.md)
  - 在 I3 下，$J_{13}(\gamma_{16})$ 以下可实现 25 行 BLP 图案 $P_{25}$，由此得 $q(5)>2^{f(P_{25},8)}$。[25 行 BLP 证明](laver_table_lower_bounds/lower_endpoints/blp.zh-CN.md)
  - 若第 11 行第 16 列非零，其二进赋值大于 $F_{\lim(\mathrm{BMS})+1}(120)$。[有限表定理（Lean）](laver_table_lower_bounds/lower_endpoint_lean/README.zh-CN.md)

- **Laver 表的精确值**

  - 在 I3 下，$J_{11}(\gamma_3)=\gamma_{2^{2048}}$。[精确值证明](exact-values/j11-gamma3/README.zh-CN.md)

- **$BB(27)>q(5)$**

  - 若 $q(5)$ 存在，这台 27 态机从空带启动，停机时恰有 $2^{q(5)}+3$ 个 1。[机器与证明](busy-beaver/q5-27/README.zh-CN.md)

## 首行周期达到 32 需要多高的阶数？

**只要 $q(5)$ 存在，就有**

$$
\boxed{\displaystyle q(5)>F_{\lim(\mathrm{BMS})+\omega+1}(3).}
$$

**无需 I3，已经 Lean 核验。** $q(5)$ 是普通二元 Laver 表的首行周期第一次达到 32 的阶数，第 $m$ 阶表有 $2^m$ 个元素。$F$ 是 FGH（fast-growing hierarchy，快速增长层级），$\lim(\mathrm{BMS})$ 是 BMS（Bashicu matrix system）的极限。为便于形式化，这里只取了一个极弱的下界。在 I3 下已经证明的更大下界见下文。[有限表陈述与证明导读](q5/README.zh-CN.md) · [Lean 定理](laver_table_lower_bounds/lean/LaverLowerBounds/OriginalBMSBound.lean)

## BMS 给 $q(5)$ 的下界极为宽松，远在首行周期达到 32 之前，端点 $J_{13}(\gamma_{16})$ 就已容纳远超 BMS 的结构

把生成临界点从零开始递增编号为 $\gamma_0,\gamma_1,\ldots$。$J_a$ 表示生成嵌入 $j$ 的第 $a$ 个左幂。写 $J_{13}(\gamma_{16})=\gamma_N$，则在 ZFC + I3 下，

$$
\boxed{\displaystyle q(5)>N>F_C(6),\qquad C=\varepsilon_{\lim(\mathrm{BMS})+1}.}
$$

$\varepsilon_{\lim(\mathrm{BMS})}=\lim(\mathrm{BMS})$，所以 $C$ 是 BMS 极限之上的第一个 $\varepsilon$ 数。$F_C$ 取塔下界证明中的基本列。实际给出这个下界的是更小的端点 $b(\gamma_3)$，其中 $b=(J_{11}(J_3))(J_7)$。[FGH 下界](laver_table_lower_bounds/lower_endpoints/bms.zh-CN.md)

写 $\kappa_i$ 为 $j$ 的临界序列，其中 **$\kappa_2=\gamma_2$，$\kappa_3=\gamma_4$**。从 $q(5)$ 对应的临界点往下逐项比较，得到

$$
\begin{aligned}
\gamma_{q(5)-1}=\kappa_4
 &> J_5(\kappa_2)>J_7(\gamma_{256})>J_7(\kappa_3)\\
 &> J_9(\kappa_3)>J_{11}\bigl(J_{11}(\kappa_3)\bigr)>J_{10}(\kappa_3)\\
 &> J_{11}(\kappa_3)>J_{13}(\gamma_{16})\\
 &> b(\kappa_3)>b(\gamma_3)>\gamma_{F_C(6)}.
\end{aligned}
$$

整条链及最后的 FGH 下界有 ZFC + I3 下的纸面证明。高段若干比较另有有限表的 Lean 证明。[逐段出处](endpoints/README.zh-CN.md) · [最后一段的证明](laver_table_lower_bounds/lower_endpoints/bms.zh-CN.md)

### 同一问题的 BLP 下界

从 $b(\gamma_3)$ 继续往下，令 $e=b(j)$，可以逐一定位实际的 BLP 图案。

$$
\begin{aligned}
b(\gamma_3)
 &>\underbrace{b(\kappa_2)}_{25\text{ 行 BLP}}
  >\underbrace{e(\gamma_{1024})}_{7\text{ 行}}
  >\underbrace{e(\gamma_{513})}_{4\text{ 行}}\\
 &>\underbrace{e(\gamma_{512})}_{3\text{ 行}}
  >J_{11}(\gamma_3)=\gamma_{2^{2048}}.
\end{aligned}
$$

25 行端点 $b(\kappa_2)$ 的编号至少为 $2^{f(P_{25},8)}$，其中 $f$ 计入普通 BLP 后续规则的作用，包括补全。**我们猜想，反复补全会使 BLP 的实际增长远超 BMS。** 已经证明这些操作可以在该端点内实现。要比较两条下界的数值，还需要量化补出的行经过后续复制和修改，累计能贡献多大的增长。[25 行 BLP 及带标记版本](laver_table_lower_bounds/lower_endpoints/blp.zh-CN.md) · [七行、四行、三行的端点证明](endpoints/lower-blp-points.zh-CN.md)

## 第 11 行第 8 列的精确值

在 I3 下，$\displaystyle J_{11}(\gamma_3)=\gamma_{2^{2048}}$。把这个点的编号简写为 $11_{2.5}$，就有 $11_{2.5}=2^{2048}$。换成有限表的语言，采用模 $2^m$ 的编号，**第 11 行第 8 列恰在第 $2^{2048}+1$ 阶第一次非零**。这个等号已经 Lean 核验。[纸面证明](exact-values/j11-gamma3/proof.zh-CN.md) · [Lean 定理与重建方法](exact-values/j11-gamma3/README.zh-CN.md)

## 一台把 $q(5)$ 写在纸带上的 27 态机

这台二符号机从全零纸带启动，当且仅当 $q(5)$ 存在时停机。停机时恰有 $2^{q(5)}+3$ 个 1。记 $\Sigma(27)$ 为最多能留下的 1 数，$BB(27)$ 为最多能运行的步数。每步至多新写一个 1，因此只要 $q(5)$ 存在，就有

$$
BB(27)\ \ge\ \Sigma(27)\ \ge\ 2^{q(5)}+3\ >\ q(5).
$$

在 ZFC + I3 中，首行周期无界保证这台机器停机。[构造与纸面证明](busy-beaver/q5-27/proof.zh-CN.md) · [54 条数字转移](busy-beaver/q5-27/transitions.txt) · [模拟器可读原表](busy-beaver/q5-27/machine.tm) · [有界复算](busy-beaver/q5-27/verification/verify.py)

## 相关结果

- **第 11 行第 16 列。** 若第 $m$ 阶该表项非零，则 $F_{\lim(\mathrm{BMS})+1}(120)<v_2(A_m(11,16))<m$。只需该表项非零，已有 Lean 证明。[定理与假设](laver_table_lower_bounds/lower_endpoint_lean/README.zh-CN.md)
- **更大输入和基础引理。** 纸面证明还给出 $\lim(\mathrm{BMS})+\omega+1$ 层级上的大输入下界，以及从固定指标的 BMS 展开次数到增长函数值的比较。[动态 BMS 证明](laver_table_lower_bounds/02-bms-feedback.zh-CN.md) · [固定指标引理](laver_table_lower_bounds/common/bms-fixed-index.zh-CN.md)

下界论文与原有 Lean 工程取自序数记号仓库的同一个版本。本图谱收录了论文、较小端点 PDF 及辅助底稿的中英两版。[下界资料总目录](laver_table_lower_bounds/README.zh-CN.md) · [较小端点 PDF](laver_table_lower_bounds/lower_endpoints/README.zh-CN.md) · [来源版本](https://github.com/hzyhhzy/column-ordinal-notations-hzy/tree/dd652aea4ac52d901b22eeff83b4196f9e5f6312/laver_table_lower_bounds)
