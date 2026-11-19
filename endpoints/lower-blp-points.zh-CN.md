# 完整 BLP 端点以下的三个较低迭代端点 · [English](lower-blp-points.md)

2026-11-09。固定 I3 嵌入 j，在同一个 Iter(j) 与临界谱 γₙ 中工作。
这是纸面推导及有限代数审计，不是纯 ZFC 翻译或 Lean 形式化。

## 1. 结论和尚未解决的定位

记 J₁=j、Jₐ₊₁=Jₐ(j)，嵌入间括号表示 application，普通复合另写 ∘。令

$$
Q=J_{11}(J_3),\quad U=Q(\gamma_{16}),\quad
b=Q(J_7),\quad e=b(j),\quad \xi=b(\gamma_2),
$$

$$
\chi=Q(\gamma_4),\qquad \Sigma=J_{13}(\gamma_{16}).
$$

新的较短表达为

$$
\boxed{\nu_1=e(\gamma_{512}),\qquad
\nu_2=e(\gamma_{513}),\qquad
\nu_3=e(\gamma_{1024}).}
$$

它们满足

$$
\boxed{\chi<\nu_1<\nu_2<\nu_3<\xi<\Sigma.} \tag{1}
$$

| 端点 | 实际承接的图案 | 临界索引下界 |
|---|---|---|
| $\nu_1=\gamma_{v_1}$ | 三行规范 $p_1$，初始 linedness 为 8 | $v_1\ge 2^{g^{[256]}(8)}>2\uparrow\uparrow259$，其中 $g(m)=m\cdot 2^m$ |
| $\nu_2=\gamma_{v_2}$ | 四行 $p_{\mathrm{start}}.\mathrm{del}$，初始 linedness 为 8 | $v_2\ge m_{\omega+2}(2)$，使用参数降为 1 后的公开变换 |
| $\nu_3=\gamma_{v_3}$ | 七行 $p_{\mathrm{init}}$，初始 linedness 为 8 | $v_3\ge 2^{f(p_{\mathrm{init}},8)}$ |

这里的下界是端点的**自然数临界索引**，不是把不可数序数本身与自然数比较。
m 是 Qi 文中的 Steinhaus–Moser 层级，f 是普通 BLP 的定量函数。

已经知道 χ<U<Q(γ₂₅₅)<ξ。U 与 ν₁、ν₂、ν₃ 的交叉次序仍是开放问题。
所以这些是完整 25 行端点 ξ 以下的三个已实现的较低承载点；不能把它们都说成
已经证明位于 U 上方的点，也不能用其强下界宣布 U 的下界得到了改进。
U 的等号问题仍未解决：现有显式结论仍为 u≥2^524288，其中 U=γᵤ。

## 2. 使用已有较低入口，避免错误的全局替换

使用已证实际入口

$$
q=J_{13}(J_{14})(J_{12}),\qquad q\equiv_\Sigma Q,
$$

$$
\mu=\gamma_{256},\quad \delta=q(\gamma_3)=\gamma_{257},\quad
q(\gamma_4)=\chi,\quad q(\mu)=\Sigma.
$$

以下先使用

$$
G=q(j),\quad G_2=q(J_2)=G(G),\quad
b_*=q(J_7),\quad e_*=b_*(j),\quad
\mathcal T=e_*(G_2),\quad H=\mathcal T(j).
$$

已有严格点像为

$$
G:\gamma_0\mapsto\gamma_1\mapsto\mu\mapsto\chi,
\quad\operatorname{cr}e_*=\delta,
\quad e_*(\delta)=\chi,\quad e_*(\chi)=\xi,
$$

$$
\operatorname{cr}\mathcal T=\gamma_1,\quad
\mathcal T(\gamma_1)=\mu,\quad \mathcal T(\mu)=\xi,
\quad H(\gamma_0)=\mu,\quad H(\gamma_1)=\chi.
$$

这些入口、最后一个点像的严格截断读值，以及初始 8-line，见
[完整 25 行搬运证明](notes/blp25-strict-transfer.zh-CN.txt) §§1–4。
这里不是声称 q=Q；事实上 q(μ)=Σ<Q(μ)。

令

$$
(\theta_0,\ldots,\theta_6)=
(\gamma_0,\gamma_1,\mu,\chi,H(\mu),H(\chi),H(H(\mu))).
$$

于是 G 将 θ₀、θ₁、θ₂ 分别送到 θ₁、θ₂、θ₃；
H 将 θᵢ 送到 θᵢ₊₂。协变性还给出

$$
\theta_4=\mathcal T(\gamma_2),\qquad
\theta_6=\mathcal T(\gamma_4)<\mathcal T(\mu)=\xi. \tag{2}
$$

θ₀<⋯<θ₆ 均为实际临界点。

## 3. 为什么三个输入恰好是 512、513、1024

[最后一个线性块证明](notes/q16-last-block-lower-bound.zh-CN.md) §2 给出

$$
G_2(\gamma_r)=\gamma_{256r}\quad(0\le r<256). \tag{3}
$$

该式也适用于这里的较低入口：所用读值均严格低于 Σ。
由于 e_* 固定 γ₂、γ₄，application 的协变性和 (2)、(3) 给

$$
\theta_4=e_*(\gamma_{512}),\qquad
\theta_6=e_*(\gamma_{1024}). \tag{4}
$$

中间的 θ₅ 不能误认成 $\mathcal T(\gamma_3)$。置

$$
D=G(j),\qquad A=G_2(j),\qquad \zeta=\gamma_{65536}.
$$

G₂≡_ζD，故 A≡_ζD(j)。已有 G 的实际有限商标准形
2²⁵⁶−3 在这个截断上适用（见
[既有标准形证明第四节](notes/after-c6-supremum-lift.zh-CN.txt)），因此

$$
A\equiv_\zeta J_{2^{256}-1}.
$$

[Dougherty II，Lemma 6.2](https://arxiv.org/pdf/math/9503204) 取 s=256、n=8，
其有效范围是输入 r<512。特别地

$$
J_{2^{256}-1}(\gamma_{257})=\gamma_{513}<\zeta,
$$

故输出严格处于截断内，可读出

$$
A(\delta)=\gamma_{513}. \tag{5}
$$

又 e_*(j)≡_δj，沿 $\mathcal T$ 搬运并使用左分配律，得

$$
e_*(A)=\mathcal T(e_*(j))
\equiv_{\mathcal T(\delta)}\mathcal T(j)=H.
$$

这里 H(χ)=θ₅<ξ=$\mathcal T(\mu)$<$\mathcal T(\delta)$，
所以仍是严格受保护的读值。由 χ=e_*(δ)、(5) 得

$$
\boxed{\theta_5=H(\chi)=e_*(A)(e_*(\delta))
=e_*(A(\delta))=e_*(\gamma_{513}).} \tag{6}
$$

最后，q≡_ΣQ 在 application 第一参数中保持截断，故 e_*≡_Σe。
(4)、(6) 的所有输出都小于 ξ<Σ，可将 e_* 换回短词 e。
这证明 νᵢ=θᵢ₊₃ 及 (1)。

## 4. 三行图案已经提供真正的迭代放大

在 θ₀,…,θ₄ 上，实际 owners 为 G、G、H：

| 行 | 步长 | owner |
|---|---:|---|
| 012 | 1 | G |
| 0123 | 1 | G |
| 01234 | 2 | H |

这就是规范 p₁，不需要构造 25 行图案。初始 θ₀、θ₁、θ₂ 的 linedness 为 8。
由 [Qi，定义 2.24、定理 2.25 和引理 2.5](https://arxiv.org/html/2501.06733v5)，
置 g(m)=m·2ᵐ，有

$$
f(p_1,8)=g^{[2^8]}(8)=g^{[256]}(8),\qquad
v_1\ge 2^{g^{[256]}(8)}. \tag{7}
$$

这里的 $g^{[256]}$ 表示 $g$ 的 256 次迭代，每次迭代的输入是前一次的输出。

设 $t_1=2$、$t_{r+1}=2^{t_r}$。由 $8>t_2$ 和 $g(x)\ge 2^x$，逐步迭代得 $g^{[256]}(8)>t_{258}$。两边取以 2 为底的指数，就有

$$
\boxed{v_1>2\uparrow\uparrow259.} \tag{8}
$$

没有计算这些巨大整数；(7)、(8) 都是符号推导。

## 5. 再保留一行和再保留四行

加上 owner H 的 012345:2，得到 θ₀,…,θ₅ 上的 p_start.del。
**它不是规范 p₂**：规范 p₂ 的末行是 01245:2。

这四行在初始参数 8 下实现，也能将初始链参数降为 1：按 Qi 定义 2.2 后的
降参数构造，把链末两项 lₘ₋₁、lₘ 换成 lₘ(lₘ)(lₘ₋₁)，反复执行即可。
这里使用 application，不能简单用普通复合代替并假定第一个点像不变。
Qi 的 Proposition 1.3(1) 证明给出固定的四次 M、三次 E(1)，
把 p_start.del 化为 p_{ω+2}，保留末端和参数 1。
其 Lemma 3.3 因而给

$$
\boxed{v_2\ge 2^{f(p_{\omega+2},1)}=m_{\omega+2}(2).} \tag{9}
$$

这是将公开转换用到本篇已经实现的低端四行图案；没有假定不同初始参数的
所有 BLP 运算自动具有某种未证单调性，也没有声称 f(p_start.del,8) 的精确值。

若使用 θ₆，则沿已有 p_init 构造插入两个内部点，即得到七行完整 p_init，
末点仍为 θ₆=ν₃，初始参数仍为 8。因此

$$
\boxed{v_3\ge2^{f(p_{init},8)}.} \tag{10}
$$

七行的全部边及 owners 见前引 25 行证明 §4。随附脚本核查了该单段。
本篇只取三行、四行、七行作为不同复杂程度的入口，不声称哪一个是最小可能端点，
也不给它们的强度作上界。

## 6. 验证范围和后续问题

[check_lower_iteration_endpoints.py](checks/check_lower_iteration_endpoints.py) 与
[运行记录](checks/check_lower_iteration_endpoints.json) 核查了：

- 三个点的短式恒等式和严格次序；
- 旧词与较低入口间每次输出读取的截断守卫；
- 三行 8 条、四行 12 条、七行 24 条实际步长边及各行 critical；
- 未给 U 与三个新点预置任何交叉次序，最终三个比较均为 UNRESOLVED。

运行约 1 秒，100 个点名、50 个 owners、348 条点像事实。没有计算巨大 Laver 表，
没有执行长下降。移位定理、初始 8-line、BLP 定量定理和标准形来自上述纸面输入；
脚本不是这些输入的独立形式化证明。

U 与 ν₁ 的比较会给出进一步的定位。若 ν₁≤U，则 (7) 会直接改进 U 的下界。
若 U<ν₁，则 ν₁ 是一个明确高于 U、低于完整 BLP 端点 ξ 的较小迭代承载点。
这两个方向目前都没有证明，不能用 ν₁ 的较强已知下界替代这个比较。

## 7. 将 γ₅₁₂、γ₅₁₃ 改写成只含小下标的式子

这两个输入都可以只用小下标写出。

$$
\boxed{\gamma_{512}=\bigl(J_{13}(J_{15})\bigr)(\gamma_2),}
$$

$$
\boxed{\gamma_{513}=\Bigl(\bigl(J_{13}(J_{15})\bigr)(J_3)\Bigr)(\gamma_1).}
$$

更对称地，置 R=J₁₃(J₁₅)、K=R(J₃)，则

$$
\boxed{\gamma_{512}=K(\gamma_0),\qquad\gamma_{513}=K(\gamma_1).} \tag{11}
$$

证明只需要[已有精确缩放结论第四节](notes/after-c6-supremum-lift.zh-CN.txt)：

$$
R(\gamma_r)=\gamma_{256r}\quad(0\le r<256).
$$

本处实际只取 r=0、1、2、3，全部输出严格小于该旧证明的截断 γ₆₅₅₃₆。
又 J₃(γ₀)=γ₂、J₃(γ₁)=γ₃，因此 application 协变性给

$$
K(\gamma_0)=K(R(\gamma_0))=R(J_3(\gamma_0))=\gamma_{512},
$$

$$
K(\gamma_{256})=K(R(\gamma_1))=R(J_3(\gamma_1))=\gamma_{768}.
$$

K 将临界谱严格递增地映入临界谱。设 K(γᵣ)=γ_{k(r)}，则
k(0)=512、k(256)=768；输入与输出的自然数索引差同为 256。
每一步增量至少为 1，故 256 步必须全部恰好增加 1：

$$
\boxed{K(\gamma_r)=\gamma_{512+r}\quad(0\le r\le256).} \tag{12}
$$

取 r=1 即得 (11)。这里没有把未受保护的 application 当成普通复合，
也没有由“小参数样例”外推等号；索引区间填满论证本身给出了精确值。
两种写法的显式下标最大均为 15，可以直接代入 ν₁、ν₂ 的公式。
