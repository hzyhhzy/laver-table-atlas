# 扩大到 260 的单层像搜索：新排除结果与未决范围

2026-11-09。固定 I3 嵌入 $j$ 的通常呈现。本文是纸面推导，
不是新增 Lean 形式化，也未声称完成纯 ZFC 有限表翻译。

记 (J_1=j, J_{a+1}=J_a(j))，嵌入之间的括号表示 application；

$$
\chi=J_{11}(\gamma_3),\qquad
\Sigma=J_{13}(\gamma_{16}),\qquad
\Theta=J_{11}(\gamma_4).
$$

用户要找的是单层式子 $J_a(\gamma_b)$，两参数不超过 260，
满足 $\chi<J_a(\gamma_b)<\Sigma$。已知的多因子 application
词即使很短，也不作为这一问题的解。

**本轮实际结论：对所有 $1\le a\le16$ 和所有自然数 (b)，
这样的式子不存在。** 新步骤是排除 (J_{12},J_{14}) 在输入
$\gamma_{16}$ 至 $\gamma_{256}$ 之间留下的可能性。
对 $17\le a\le260$ 的搜索尚不完备；没有发现见证不等于证明不存在。

## 1. 依赖和记号

基础来源：

- [Dougherty I，第 5 节](https://arxiv.org/pdf/math/9205202)。
- [Dougherty II，Lemma 6.2、第 8 节及截断规则](https://arxiv.org/pdf/math/9503204)。
- [先前缺口证明](j13-gamma13-15-below-chi.zh-CN.txt)。
- [Q 的完整低端数位谱证明](c5-linear-prefix-and-q-spectrum.zh-CN.txt)。

下文确实依赖最后一项的纸面定理，不把若干样例计算当成它的证明。

置

$$
K=J_{11},\ A=J_{12},\ B=J_{13},\ E=J_{14},\ F=J_{15},
\quad \mu=\gamma_{256},
$$

$$
\sigma=j(<\kappa_1),\quad\sigma_2=j(<\kappa_2),\quad
\tau=j(\sigma),\quad S_i=J_i(\sigma),\quad T=A(\sigma_2).
$$

其中 $f(<\alpha)=\sup_{\beta<\alpha}f(\beta)$，
$\kappa_0=\gamma_0,\kappa_1=\gamma_1,\kappa_2=\gamma_2,
\kappa_3=\gamma_4$。既有结论为

$$
\gamma_3<S_3<S_2<\tau<\sigma_2<\kappa_3,
\quad T=B(<\kappa_3)<S_{11}=A(<\kappa_3)<\mu.
\tag{1}
$$

令 $s=B(\sigma)$。先前缺口证明给出

$$
s=A(\tau)=j(S_2),\qquad
\gamma_{15}<s<\gamma_{16},
\tag{2}
$$

$$
B(<s)<A(\gamma_{16})<\chi<B(s),
\qquad A(<S_{11})<\chi.
\tag{3}
$$

这里 (s=j(S_2)) 使用 $B|V_{\kappa_2}=(j\circ J_2)|V_{\kappa_2}$
及 $\sigma<\kappa_2$。这些是普通限制的使用，不把其端点直接代入。

## 2. 把几个非临界分界点定位到 gamma255 与 gamma256 之间

首先有 $S_{14}=E(\sigma)=J_2(S_2)$。理由是已知

$$
E\equiv_{\gamma_8}J_2\circ J_2,\qquad E(\kappa_2)=\gamma_8.
$$

对输入 $\sigma<\kappa_2$，一侧输出 $E(\sigma)<\gamma_8$，
故成员截断的严格输出守卫允许读出这个等号。

由 (F=E(j)) 的协变性，

$$
F(S_{14})=E(j(\sigma))=E(\tau)>E(\gamma_3)=\gamma_{12}.
$$

Dougherty II Lemma 6.2 给出 $F(\gamma_7)=\gamma_{11}$
（此处移位量为 4，输入 7 严格小于 8）。因 (F) 严格递增，

$$
\gamma_7<S_{14}.
\tag{4}
$$

令 (Q=B(J_2)=E(E))，(v=B(S_2))。所引数位谱定理给出

$$
Q(\gamma_{255})=\gamma_{13107}.
\tag{5}
$$

协变性、(4) 以及已经证明的 $B(\gamma_7)=\gamma_{16384}$ 给出

$$
Q(v)=B(J_2(S_2))=B(S_{14})
>B(\gamma_7)=\gamma_{16384}>Q(\gamma_{255}).
$$

所以 $\gamma_{255}<v$。再用 (1)，得到严格链

$$
\boxed{\gamma_{255}<B(S_2)<B(\tau)<T<S_{11}<\gamma_{256}.}
\tag{6}
$$

$B(\tau)<T=B(<\kappa_3)$ 的严格性可取一个位于
$\tau$ 与 $\kappa_3$ 之间的序数再使用单调性；不是仅由上确界
定义直接把小于等于写成严格小于。

## 3. 排除 J12 的所有输入

(6) 与 (3) 给出

$$
A(\gamma_{255})\le A(<S_{11})<\chi.
\tag{7}
$$

另一方面，(A=K(j))、$K(\kappa_2)=\mu$ 给出

$$
A(\gamma_{256})=A(K(\kappa_2))=K(j(\kappa_2))
=K(\kappa_3)=\Theta>\Sigma.
\tag{8}
$$

由严格递增性，整数输入在 $b\le255$ 时全部小于左端点，
在 $b\ge256$ 时全部大于右端点。因此此整行不存在所求式子。

## 4. 排除 J14 的所有输入

本节额外检查上确界的严格性，不能从 $j$ 严格递增直接推出
(j(<S_2)<j(S_2))。

因为  $\operatorname{cf}(\sigma)=\kappa_1$，初等性给出

$$
\operatorname{cf}(S_2)=J_2(\kappa_1)=\kappa_2.
$$

$\kappa_2$ 正则且 $j(\kappa_2)=\kappa_3>\kappa_2$。取长
$\kappa_2$ 的共尾序列并施以 $j$，其前 $j``\kappa_2$ 部分
在长 $j(\kappa_2)$ 的像序列中有界，从而

$$
j(<S_2)<j(S_2)=s.
\tag{9}
$$

上确界搬运公式与 (E=B(j)) 给出

$$
E(<v)=B(j(<S_2))\le B(<s)<\chi.
\tag{10}
$$

由 (6)，

$$
E(\gamma_{255})\le E(<v)<\chi.
\tag{11}
$$

到下一整数输入时，使用 $B(\kappa_3)=\mu$：

$$
E(\gamma_{256})=E(B(\kappa_3))=B(j(\kappa_3))
=B(\kappa_4)>\kappa_4>\Theta>\Sigma.
\tag{12}
$$

故 (J_{14}) 整行同样被排除。

## 5. 其余 a<=16 的全行排除

[先前 272 项分类](no-single-j-gamma16-between-chi-Sigma.zh-CN.txt)
已经处理了 $b\le16$。对下面各行，已知严格超过 $\Theta$
的最小输入不超过 16：

| a | 一个已证超过 Theta 的输入 b |
|---|---|
| 1,2,3,4 | 4 |
| 5,6 | 2 |
| 7 | 3 |
| 8 | 6 |
| 9,10 | 3 |
| 11 | 5 |
| 15 | 16 |
| 16 | 8 |

所以这些行余下的输入全部超过 $\Sigma$。第 13 行在 $b=16$
恰等于 $\Sigma$，以后严格超过它。第 12、14 行由第三、四节处理。
这就证明了本文件开头的全称排除。

## 6. 扩大搜索的准确范围

`search_single260.py` 使用协变性、严格单调性、明确的低端等号、
有截断守卫的应用块恒等式建立一个有限部分序。它不是整个矩形的
决定程序，程序未能比较的点保持未决。自然数有限表中的乘积为零，
只说明在该阶饱和，不证明它超过 $\chi$ 或 $\Sigma$。

目前尚未得到 $1\le a\le260, 0\le b\le260$ 中的见证。
一个较小的未决点是

$$
J_{24}(\gamma_4)=J_{25}(\gamma_2)=J_{26}(\gamma_2)
=J_{27}(\gamma_2)=J_{28}(\gamma_5).
$$

这些等号由 successive application 的协变性及
$J_{24}(\gamma_2)=\gamma_2, J_{25}(\gamma_1)=\gamma_2,
J_{26}(\gamma_1)=\gamma_2, J_{27}(\gamma_1)=\gamma_5$
读出。它只是同一未决点的多种写法，没有证明它落在目标区间内。

`probe_suprema260.py/.json` 记录第二至四节的有限关系审查。
脚本引用了 (4)、(9)—(10) 的纸面推导作为明确前提；
因此脚本通过不构成对这些上确界前提的独立形式化证明。
