# 第八像的等号：$J_{13}(\gamma_8)=\gamma_{65536}$

2026-11-09。这份演算在固定 I3 嵌入 $j$ 下证明了 $J_{13}(\gamma_8)=\gamma_{65536}$。随后完成的证明给出 $J_{11}(\gamma_3)=\gamma_{2^{2048}}$，并在 Lean 中核验了这个等号。[后续证明与核验记录](../../exact-values/j11-gamma3/README.zh-CN.md)

核心有限表恒等式是

$$
  65534*_{65537}65534=2^{256}-65536. \tag{S}
$$

此前已经证明同一等式在所有不超过 65536 的阶数成立。本次只增加
一个阶数，但这个最高位正是决定第八像的那一位。

## 1. 约定与已证输入

$J_a$ 是应用左幂：$J_1=j, J_{a+1}=J_a(j)$。
应用、通常函数复合、序数求值三者不混用。
$A_d$ 有 $2^d$ 个元素，用 $0,\ldots,2^d-1$ 表示；
$a*_d1=a+1\pmod {2^d}$。
$e\equiv_{\gamma_d}f$ 表示 Laver 成员关系截断，等价于相同有限表剩余。
$f_e(r)$ 由 $e(\gamma_r)=\gamma_{f_e(r)}$ 定义。

记

$$
 d=65537,\quad B=2^{65536},\quad z=2^{256},
 \quad L=65534,\quad v=z-65536,\quad g=z-3.
$$

以下输入的证明均早于本文：

1. [D2] 的位支撑包含、临界点像只能落在零位、周期和临界点像的对应、
   Lemma 7.1、Theorem 7.2、Corollary 6.4、Lemma 6.7。
2. 指数增长及取等刚性：若 $f_e(0)=1,f_e(1)=m\ge2$，则
   $f_e(r)\ge m^r$。若在 $r\ge2$ 处取等，则
   $e\bmod 2^{m^r+1}=2^m-3$。
3. 连续位块下界：对允许宽度 $N=2^{2^t}$，若低 $N$ 位在
   $1,\ldots,2^N-3$ 内，第 $N,\ldots,M-1$ 位全为 1，则
   $e(\gamma_N)\ge\gamma_{M^2}$。
4. 宽 16 的稠密高位引理：若第 16 至 255 位至少有 16 个 1，
   低 16 位在 $1,\ldots,65533$ 内，则
   $e(\gamma_{16})\ge\gamma_{65536}$。低位为 65534 且
   $e(\gamma_1)<\gamma_{256}$ 时也成立。
5. 旧前缀定理：令 $h=h_{16}$ 把每个二进制位重复 16 次，则
   $J_L(J_r)\equiv_{\gamma_{65536}}J_{h(r)}$，$1\le r\le65534$。
6. 上一轮独立证明的高位乘积

$$
     v*_{65537}65533=B+g. \tag{V}
$$

   此式仅用旧前缀定理，不用 $S$。同一文件还证明
   $J_{13}(\gamma_8)=\gamma_{65536}\iff\text{(S)}$。

输入 2 见 `exclude-2pow2048-rigidity.zh-CN.txt`。
输入 3–5 见相邻只读目录中的
`c4-filled-block-period-bridge.zh-CN.txt`、
`c4-density-and-odd-carries.zh-CN.txt`、
`c4-gamma4096-even-carries.zh-CN.txt`。
输入 6 见本目录 `one-carry-eliminated.zh-CN.txt`，特别是第 3–5 节。

下文反复使用两条临界桥链：

$$
 \mathcal C_{16}=(0,1,4,8,12,14,15),
$$

$$
 \mathcal C_{256}'=(16,64,128,192,224,240,248,252,254,255).
$$

对链中相邻索引 $a,b$，存在嵌入的临界序列分别以
$\gamma_a\to\gamma_b\to\gamma_{16}$ 或
$\gamma_a\to\gamma_b\to\gamma_{256}$ 开头。
第二条链的前两对来自 [D2] Theorem 7.2$a$，取 $n=3,m=1,0$：

$$
 2^{2^n-2^{m+1}}\longrightarrow 2^{2^n-2^m}
       \longrightarrow 2^{2^n}.
$$

其余对来自 Theorem 3.1$a$，取 $n=8,m=6,5,\ldots,0$。
链的存在性不依赖待证等号。

## 2. 新的严格临界点引理

**引理 1。** 若

$$
 16\le r<256,\qquad \operatorname{cr} e=\gamma_r,\qquad
 e(\gamma_r)\ge\gamma_{256},
$$

则

$$
 e(\gamma_{256})>\gamma_{65536}. \tag{J+}
$$

先证 $r=16$。写 $e(\gamma_{16})=\gamma_b$，$b\ge256$。
若 $b>256$，首个临界像的连续 1 位刻画，配合宽 256 的连续位块
下界，给出 $e(\gamma_{256})\ge\gamma_{b^2}>\gamma_{65536}$。

现在设 $b=256$。取 $a=J_{65533}$。由 [D2] Theorem 7.2$c$
和 $a(j)=J_L$，$a$ 的前三个谱像为 $1,16,256$。
$e$ 固定 $\gamma_0,\gamma_1,\gamma_2$，所以 $F=e(a)$ 的前三个像为

$$
  \gamma_1,\quad\gamma_{256},\quad e(\gamma_{256}).
$$

指数下界先给出 $e(\gamma_{256})\ge\gamma_{65536}$。若取等，取等刚性强迫

$$
  F\bmod 2^d=g.
$$

位支撑包含 $\operatorname{bits}(e)\subseteq
\operatorname{bits}(F-1)$（取同一有限剩余）说明 $e$ 在第 256 至 65536
位全为 0。另一方面，临界点为 16、首像为 256，说明低 16 位全为 0，
第 16 至 255 位全为 1。因此 $e\bmod2^d=v$。于是

$$
 F\bmod2^d=v*_d65533=B+g,
$$

与取等刚性矛盾。这完成 $r=16$ 的证明。

沿 $\mathcal C_{256}'$ 传播此结论。假设已证临界点为 $\gamma_\alpha$
的情形，下一链点为 $\beta$。对任意 $\alpha<r\le\beta$，取临界桥
$t:\gamma_\alpha\to\gamma_\beta\to\gamma_{256}$。
$e$ 固定 $\gamma_\alpha$，所以 $H=e(t)$ 的临界点为
$\gamma_\alpha$，首像为 $e(\gamma_\beta)\ge\gamma_{256}$。归纳假设给出

$$
 H(\gamma_{256})>\gamma_{65536}.
$$

协变性与单调性给出

$$
 e(\gamma_{256})=H(e(\gamma_\beta))
 \ge H(\gamma_{256})>\gamma_{65536}.
$$

有限个区间覆盖 16 至 255，故引理得证。

## 3. 偶数步的全部保护点越过端点

**引理 2。** 若 $s$ 为 16 的倍数，$16\le s<256$，且

$$
 k\bmod2^{s+16}=2^sx+2^s-1,\qquad 1\le x\le65534,
$$

则

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{Shift+}
$$

对 $x$ 向下归纳；高于 $s+16$ 的位任意。
基例 $x=65534$ 给出 $k(\gamma_0)=\gamma_s$、
$k(\gamma_1)\ge\gamma_{s+16}$。线性增长因此给出

$$
 k(\gamma_{15})\ge\gamma_{s+240}\ge\gamma_{256}.
$$

沿 $\mathcal C_{16}$ 跨越 $\gamma_{256}$，取相邻的
$\alpha,\beta$ 与相应临界桥 $t$，使

$$
 \gamma_s\le k(\gamma_\alpha)<\gamma_{256}
       \le k(\gamma_\beta).
$$

嵌入 $H=k(t)$ 的临界点索引在 $[16,256)$，首像不低于 256。
引理 1 给出 $H(\gamma_{256})>\gamma_{65536}$，故
$k(\gamma_{16})=H(k(\gamma_\beta))>\gamma_{65536}$。

归纳步照 [D2] Theorem 7.2 证明中的 Claim 1，得到 $H=k(t)$，满足

$$
 \gamma_s<\operatorname{cr}H<\gamma_{s+16}\le k(\gamma_\beta),
 \qquad H\bmod2^{s+16}=2^sx',\quad x<x'\le65534.
$$

令 $H'=H+2^s-1$，这里加法是反复应用后继。
归纳假设给出 $H'(\gamma_{16})>\gamma_{65536}$。Corollary 6.4 给出

$$
 k(\gamma_{16})=H(k(\gamma_\beta))
 \ge H(\gamma_{s+16})\ge H'(\gamma_{16})>\gamma_{65536}.
$$

引理得证。

现在设 $t$ 为偶数，$2\le t\le65534$。置

$$
 m=v_2(t),\quad s=16m,\quad a=h(t-2^m),\quad G=65535.
$$

$1\le m\le15$，所以 $16\le s<256$，且 $2^{s+16}\mid a$。
Lemma 6.7 中的全部保护点是

$$
 J_{a+2^s z-1}(\gamma_{16}),\qquad 2\le z\le G.
$$

其低位为 $2^s(z-1)+2^s-1$，引理 2 全部适用，保护点至少为
$\gamma_{65537}$。故

$$
 h(t-1)*_d G=h(t). \tag{Even+}
$$

## 4. 奇数步：允许不妨碍递推的周期翻倍

先加强稠密引理的例外低位情形。

**引理 3。** 若 $k\bmod2^{16}=65534$，第 16 至 255 位至少有 16 个 1，
且 $k(\gamma_1)=\gamma_b<\gamma_{256}$，则

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{DenseB+}
$$

旧稠密引理的证明已经给出 $k(\gamma_{15})\ge\gamma_{256}$。
从链点 1 到 15 跨越 256，得到 $H=k(t)$，其临界点索引在
$[b,256)\subseteq[16,256)$，首像不低于 256。引理 1 与协变性立即给出
所需严格不等式。注意这里仍明确要求 $b<256$。

**引理 4。** 若 $1\le k\bmod2^{16}\le65533$，且其第 16 至 255 位
至少有 16 个 1，第 16 位为 1，并且这 240 位不全为 1，则

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{DenseA+}
$$

使用宽 16 的标准跨越，令 $H=k(t)$，其低 16 位是严格更大的非零偶数，
且继承 $k$ 在第 16 位及以上的所有 1 位。
设临界桥为 $\alpha\to\beta\to\gamma_{16}$。
因为 $k$ 的第 16 位为 1，$k(\beta)$ 不等于 $\gamma_{16}$，从而
$k(\beta)>\gamma_{16}$。

若 $H$ 的低位不是 65534，旧稠密引理给出
$H(\gamma_{16})\ge\gamma_{65536}$，严格单调性便给出
$k(\gamma_{16})=H(k(\beta))>\gamma_{65536}$。

若 $H$ 的低位为 65534，写 $H(\gamma_1)=k(\beta)=\gamma_b$。
$b<256$ 时用引理 3；$b>256$ 时用线性增长
$H(\gamma_b)\ge\gamma_{b^2}>\gamma_{65536}$。

只剩 $b=256$。此时 $k(\alpha)=\gamma_1$、$k(\beta)=\gamma_{256}$。
假定所需严格不等式失败，旧下界保证恰好取等。
链中只有两种可能：

- $(\alpha,\beta)=(\gamma_0,\gamma_1)$：$k$ 的前两像为 1、256，
  指数增长直接矛盾。
- $(\alpha,\beta)=(\gamma_1,\gamma_4)$：$k$ 固定 $\gamma_1$，
  且 $k(\gamma_4)=\gamma_{256}$。临界点只能为 2、3、4。

第二种情况的三个子情形如下，详细的小增长引理见前一文件第 1 节。

1. 临界点为 4：首像为 256 强迫第 4 至 255 位全为 1，与高部没有填满矛盾。
2. 临界点为 3：设 $k(\gamma_3)=\gamma_m$，$m\ge4$。
   小增长引理给出 $f_k(4)\ge m^m$，$m>4$ 时严格。
   $f_k(4)=256$ 强迫 $m=4$，并且
   $k(J_3)\bmod2^{257}=11$。位支撑包含与 $k$ 的第 16 位为 1 矛盾。
3. 临界点为 2：设 $a=f_k(2)\ge3$。$c=k(j)$ 的前两像为 1、$a$，
   且 $c(\gamma_a)=\gamma_{256}$，所以 $a^a\le256$，只能 $a=3,4$。
   当 $a=3$，令 $A=k(J_3)$、$h=A(j)$、$m=f_k(3)\ge4$。
   则 $A(\gamma_3)=\gamma_{256}$，$\operatorname{cr}h=\gamma_3$，
   $h(\gamma_3)=\gamma_m$，且 $h(\gamma_m)=A(\gamma_2)<\gamma_{256}$。
   小增长引理却给出 $h(\gamma_4)\ge\gamma_{m^m}\ge\gamma_{256}$，矛盾。
   当 $a=4$，指数取等刚性给出 $c\bmod2^{257}=13$。
   但低 16 位的后继不溢出，故 $c=k+1$ 的第 16 位仍为 1，矛盾。

以上排尽所有情形，引理 4 得证。

现设 $t$ 为奇数，$3\le t\le65533$，置

$$
 a=h(t-1),\qquad m=v_2(t-1),\qquad s=16m.
$$

$a$ 的第 16 至 255 位至少含一整块 16 个 1，且这些位没有填满。
考虑递推中的各行 $a+i$，$1\le i\le65534$。

若 $m=1$，第 16 位为 1。对 $i\le65533$ 用引理 4；
$i=65534$ 时首个临界像小于 256，用引理 3。
所以这些行在 $A_d$ 中的周期都整除 $2^{16}$。
因为 $a+1\equiv1\pmod {2^{16}}$，每步递推都只加 1。

若 $m\ge2$，只用旧的不严格稠密下界即可：

$$
 J_{a+i}(\gamma_{16})\ge\gamma_{65536}
 \ \Longrightarrow\ J_{a+i}(\gamma_{17})\ge\gamma_{65537}.
$$

因此周期整除 $2^{17}$，虽然不一定整除 $2^{16}$。
但 $s\ge32>17$，仍有 $a+1\equiv1\pmod{2^{17}}$，递推照样只加 1。
于是两种情况下都有

$$
 a*_d1=a+1,\qquad
 a*_d(i+1)=(a+i)*_d(a+1)=a+i+1,
$$

并得到

$$
 h(t-1)*_dG=h(t). \tag{Odd+}
$$

这里的周期最多翻倍一次是证明的一部分；没有把所有旧保护点
无条件改成严格不等式。

## 5. 合并并接回第八像

$L*_d1=65535=h(1)$。把 $Even+$ 与 $Odd+$ 合并，对 $r$ 有限归纳，得

$$
 L*_d r=h(r),\qquad 1\le r\le65534.
$$

最后 $h(65534)=2^{256}-65536=v$，这就是 $S$。

前一文件的已证充要判据现在给出

$$
 \boxed{J_{13}(\gamma_8)=\gamma_{65536}.}
$$

因此目前已知的这一段点值可写成

$$
 J_{13}(\gamma_r)=\gamma_{4^r},\qquad 0\le r\le8.
$$

前一文件已经求得 $v*65520=2^{256}-16$，并在足够高的截断求得
$(2^{256}-16)*14=2^{256}-2$，因此接回第八像时没有新的未算乘积。

## 6. 非循环性与未决范围

依赖顺序是：旧前缀（只到 65536）→ 前一文件的 $V$ → 引理 1 →
严格位移/稠密引理 → 新前缀（到 65537）→ 第八像等号。
没有从新前缀反推它自己的输入 $V$。

不要把本文的 $d=65537$ 换成 $2^{2048}+1$。证明使用的是只增加一阶的
周期控制，不能未经证明跨越极长阶数区间。
因此本文尚未证明

$$
 J_{11}(\gamma_3)=\gamma_{2^{2048}},
$$

也没有证明它不等于该值。

在固定 I3 语境中，本文是纸面证明；涉及的前文高截断识别仍采用普通
限制及其提升。将整个依赖链翻译成无大基数的有限表证明，是另一项尚未
完成的工作。对低位模式的程序检查也不能代替上述证明。

## 7. 有界核验

eighth_image_audit.py/.json 在 0.828 秒内完成并退出。检查覆盖全部
32767 个偶数步、16383 个需要严格保护的奇数步、16383 个允许周期
多翻倍一次的奇数步，以及 1048544 个抽取的位移保护点模式。
临界桥公式核对了 9 个相邻区间，覆盖 16 至 255 的全部索引。

另按定义独立建立 $A_9,A_{10}$，检查 511 行的周期提升，其中
57 行确实翻倍，并验证 3130 个相应的模数替换。这些检查用于排除
索引和周期用法的错误；未构造 $A_{65537}$，不代替本文的纸面证明。

## 参考

- Randall Dougherty, [Critical points in an algebra of elementary embeddings, II]$https://arxiv.org/pdf/math/9503204$.
- 本目录 `one-carry-eliminated.zh-CN.txt`、`eighth-image-two-carries.zh-CN.txt`、
  `after-c6-supremum-lift.zh-CN.txt`、`exclude-2pow2048-rigidity.zh-CN.txt`。
- 相邻只读目录 `../small-jn-km-100-20261109/` 中本节开头列出的旧引理。
