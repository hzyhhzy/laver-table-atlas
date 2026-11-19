# 较低开扇形第二类型构造的严格上确界封口 · [English](root-low-Q11-strict-cap-proof.en.md)

*本稿原以英文写成。此中文阅读版使用机器辅助翻译。*

> 整理阅读版。 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-15. 新的局部定理；NOT 完整的原始-R Hardy 目标。第一个独立的代数审计已由Hardy 的兄弟姐妹通过。

这种表示方式与现有的C[4]和低开式风扇论文的表示方式完全一致：

~~~text
K=j11, b=K(j), c=K(b), d=c(K), A=c(d),
mu=K(kappa2), a=K(mu), theta8=j9(kappa3),
s=j(<kappa1), v=K(<kappa2)=j10(s).
~~~

应用为F(G)；上标为2，或者重复的点应用在下方表示ORDINARY COMPOSITION。特别地，c^2(x)=c(c(x))。切割点v并不被认为是生成的临界点。

~~~text
THEOREM.
A(v) < K^2(v) < theta8 < kappa4.          (1)
~~~

证明。已发表的近似K相当于joj，当μ低于此值时，对于每一个t<kappa2，都有j^2(t)=K(t)：K(t)<K(kappa2)=mu。因此，它们在kappa2处的严格上界是一致的：

~~~text
(j o j)(<kappa2)=K(<kappa2)=v.             (2)
~~~

这里使用的值严格低于临界值，而不是等于μ。

存在一个EXACT环境恒等式

~~~text
c=(K o K)(j),
~~~

因为普通的复合运算是通过连续应用来对嵌入代数产生影响的。因此，通过普通复合运算的分布，

~~~text
c o c=(K o K)(j o j).
~~~

将严格的sup运输恒等式应用于(2)。因为

~~~text
(K o K)(kappa2)=K(mu)=a,
~~~

我们得到了精确的切割值

~~~text
(c o c)(<a)=(K o K)(v)=K^2(v).            (3)
~~~

Regularity/discontinuity等于v<mu。因此，K(v)<a。由于a是的极限，严格递增导致c^2(K(v))<c^2(<a)。同时，c固定了v，因为crit(c)=mu。在这个固定输入下的应用兼容性表现为

~~~text
d(v)=c(K)(v)=c(K(v)),
A(v)=c(d)(v)=c(d(v))=c^2(K(v)).           (4)
~~~

方程(3)--(4)得出在(1)中的FIRST严格不等式。

对于第二个情况，使用K=j10(j)和j10=j9(j)，始终在真正的j10-或j9-image情况下使用：

~~~text
K^2(v)=K^2(j10(s))=j10(j^2(s))=j10(K(s)).
~~~

这里j^2(s)=K(s)是合理的，因为s<kappa2和K(s)<mu也是合理的。标准的严格上恒等式也表明了这一点。

~~~text
K(s)<K(<kappa2)=j10(s)<j10(<kappa2)=j9(s).
Therefore
K^2(v)=j10(K(s))<j10(j9(s))=j9(j(s))<j9(kappa3)=theta8.
~~~

最后的比较使用了s<kappa2，因此j(s)<kappa3。已发表的点不等式给出了theta8<kappa4。这证明了(1)。

低楼梯情况后果。设Q11=A(K)为其辅助函数，a为其第一个外部入口，c_exit=theta7为每一个低阶开放风扇的初始上限值，而所有低阶开放风扇的初始上限严格低于Q11(<a)。严格上传输函数给出Q11(<a)=A(K(<kappa2))=A(v)的结果。因此，ALL这样的有限初始上限值位于theta8<kappa4之下。辅助函数a固定了较低标量域kappa3，并移动了之前的第一类输入a；第一个外部入口c_exit则负责接纳之前的输出。因此，之前证明的低楼梯第二类接口现在有了其缺失的上限保护。

~~~text
Scope.
~~~

最初的论证表明，这种实际类型的二阶楼梯比旧的E(V0)结构更便宜。在DOES以下的更强连续性也证明了A(mu)<kappa4。但这两个结果都没有涵盖所有有限的类型级别，也没有涵盖完整的第一根对角线C，以及原始的R=I030。既没有出现A(<v)和A(v)之间的等式，也没有出现在其端点使用开放截面的情况。

主要输入是在Dougherty中通过视觉检查得出的近似值以及严格的上限规则，这些临界点在基本代数中具有重要意义。

~~~text
Embeddings, printed pp.22--23: https://arxiv.org/pdf/math/9205202 .
~~~

其余部分就是所展示的application/composition代数。

## 更强的持续性（由双亲独立审核）。

实际上，A(<a)<K^2(v)<theta8。(5)。这证明了对于A(x)<theta8，以及EVERY和x<a，包括实际产生的临界点A(mu)和A(theta5)，这些以前是未知的。

实际上，A=(c o c)(K) EXACTLY，因为d=c(K)。同时，c^2(mu)=a。因此，严格的上传传输给出A(<a)=c^2(K(<mu))。点mu是规则的，K(mu)=a>mu，所以标准的不连续性引理给出K(<mu)<a。因此，A(<a)<c^2(<a)=K^2(v)<theta8。这并不与A(a)>kappa4矛盾：即在大的跳跃时，值，而(5)仅涉及严格更小的输入。

初始化低风扇电容的后果：Q11 o V0：辅助项 c_exit，入口 A(mu)，闭合电容 A(theta5)<theta8。Q11 o Q11：辅助项 A(mu)，入口 A(theta5)，严格初始化的电容

~~~text
< A((K o K)(<kappa2)) < theta8.
~~~

后者使用(KoK)(<kappa2)<(KoK)(kappa2)=a；规律性再次适用。粗帽A(a)>kappa4被替换为NOT。

A是后一种切割的实际有用临界上界端点。

~~~text
rho0=j10(gamma3)<a,
~~~

因为，使用K=j10(j)和kappa2=j10(kappa1)，

~~~text
(K o K)(<kappa2)=j10((j o j)(<kappa1))<j10(gamma3)=rho0.
~~~

这里(joj)(<kappa1)<gamma3所表示的是已发表的严格不等式，而不是的点值声明j(j(s))<gamma3。同时，j10(kappa3)=a：在j10(kappa2)=mu处应用K=j10(j)，可以得到K(mu)=j10(kappa3)。因此，A(rho0)<theta8是作为生成的临界点，作为的封闭端点存在，而不是更粗糙的theta8。

[原稿快照](<root-low-Q11-strict-cap-proof.txt>)
