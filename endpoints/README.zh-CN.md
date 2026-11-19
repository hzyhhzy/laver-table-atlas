# 从周期 32 到较小临界点 · [English](README.md)

固定 I3 嵌入 $j$。写 $J_1=j$、$J_{a+1}=J_a(j)$，$\kappa_i=j^i(\operatorname{crit}j)$。嵌入之间的括号表示 application，作用在序数上的括号表示取像。把生成临界点从 $\gamma_0$ 开始递增编号，就有 $\kappa_2=\gamma_2$、$\kappa_3=\gamma_4$ 和 $\kappa_4=\gamma_{q(5)-1}$。若 $J_a(\gamma_t)=\gamma_s$，第 $m$ 阶有限表读出 $\min(s,m)$。读法是取 $A_m(a,2^t)$ 的二进赋值，表项为零时取 $m$。[共同约定](../laver_table_lower_bounds/common/conventions.zh-CN.md) · [有限表中的等式](../laver_table_lower_bounds/lean/LaverLowerBounds/LowConstants.lean)

## 高段

令 $\mu=J_7(\kappa_2)=\gamma_{256}$。严格次序可分两段读取。

$$
\begin{aligned}
\kappa_4 &> J_5(\kappa_2)>J_7(\mu)>J_7(\kappa_3)>J_9(\kappa_3),\\
J_9(\kappa_3)&>J_{11}\bigl(J_{11}(\kappa_3)\bigr)>J_{10}(\kappa_3)>J_{11}(\kappa_3).
\end{aligned}
$$

对第一行，已知 $J_5(\gamma_3)=\kappa_4$ 和 $\kappa_2<\gamma_3$。有限表的双重作用估计给出 $J_7(\mu)<J_5(\kappa_2)$。再用 $\kappa_3<\mu$ 和 $J_8(\gamma_8)=J_9(\kappa_3)$、$J_8(\mu)=J_7(\kappa_3)$，得到其余比较。对第二行，Lean 中的 `seven_lt_eight`、`six_lt_seven`、`five_lt_six` 正好是这三个严格不等式在有限表里的版本。[双重作用与点像](../laver_table_lower_bounds/lean/LaverLowerBounds/CappedAlgebra.lean) · [较高端点的完整数据](../laver_table_lower_bounds/lean/LaverLowerBounds/HigherConstants.lean)

## 低段

令 $b=(J_{11}(J_3))(J_7)$，$e=b(j)$。已有

$$
J_{11}(\kappa_3)>J_{13}(\gamma_{16})>b(\kappa_3)>b(\gamma_3)>b(\kappa_2).
$$

共同入口证明的式 (4) 给出第一个不等式。式 (8) 先对局部词 $b_0$ 给出后面各点的严格次序。由于 $b_0$ 与 $b$ 在 $J_{13}(\gamma_{16})$ 处截断相等，且这里读取的三个输出都严格低于截断点，可以依次换成 $b$ 的输出。[共同入口，式 (4)、(6)、(8)、(9)](../laver_table_lower_bounds/lower_endpoints/endpoints.zh-CN.md)

| 端点 | 已实现的下界或精确值 |
|---|---|
| $b(\gamma_3)=\gamma_s$ | $s>F_C(6)$，其中 $C=\varepsilon_{\lim(\mathrm{BMS})+1}$。[BMS 塔下界证明](../laver_table_lower_bounds/lower_endpoints/bms.zh-CN.md) |
| $b(\kappa_2)=\gamma_r$ | 25 行普通 BLP。$r\ge 2^{f(P_{25},8)}$。同一端点还实现了有明确规则的标记版本。[证明](../laver_table_lower_bounds/lower_endpoints/blp.zh-CN.md) |
| $e(\gamma_{1024})=\gamma_{v_3}$ | 七行 $p_{\rm init}$。$v_3\ge 2^{f(p_{\rm init},8)}$。[证明第 5 节](lower-blp-points.zh-CN.md) |
| $e(\gamma_{513})=\gamma_{v_2}$ | 四行图案。$v_2\ge m_{\omega+2}(2)$，其中 $m$ 是文中采用的 Steinhaus–Moser 层级。[证明第 5 节](lower-blp-points.zh-CN.md) |
| $e(\gamma_{512})=\gamma_{v_1}$ | 三行图案。$v_1>2\uparrow\uparrow259$。[证明第 4 节](lower-blp-points.zh-CN.md) |
| $J_{11}(\gamma_3)$ | 精确等于 $\gamma_{2^{2048}}$。[纸面证明与 Lean 定理](../exact-values/j11-gamma3/README.zh-CN.md) |

第一行中，$\lim(\mathrm{BMS})$ 是 $\alpha\mapsto\varepsilon_\alpha$ 的不动点，$C$ 是它之上的第一个 $\varepsilon$ 数。$F_C$ 使用塔下界证明中的基本列。[指数塔的秩与基本列](../laver_table_lower_bounds/01-blp-tower.zh-CN.md)

表中的六个端点从上到下严格递减。表中右栏是各端点分别取得的估计，各估计之间的比较需要自己的数值证明。有限表 Lean 工程核验了其中若干端点关系，并独立证明了第 11 行第 16 列在非零时的 $\lim(\mathrm{BMS})+1$ 层级下界。[Lean 结果范围](../laver_table_lower_bounds/lower_endpoint_lean/README.zh-CN.md)

[辅助演算索引](notes/README.zh-CN.md)

[返回首页](../README.zh-CN.md)
