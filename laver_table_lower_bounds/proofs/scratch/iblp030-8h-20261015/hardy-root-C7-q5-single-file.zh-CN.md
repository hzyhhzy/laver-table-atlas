# 用原版 IBLP 的六个有限类型给出 q(5) 的 Hardy 下界 · [English](hardy-root-C7-q5-single-file.en.md)

*本稿原以英文写成。此中文阅读版使用机器辅助翻译。*

> 整理阅读版。 数学结论以本目录三篇主文为准。
> 原有局部证明、适用条件和撤回提醒保留；旧进度文字仅作历史记录。
> 固定输入的历史段落如有省略，逐段位置记录于 SOURCE_MANIFEST.json；
> 主文已用原证明产生的自然参数补上相应数值推导。未新增 Lean 认证。

2026-10-15。在ZFC+I3条件下进行单文件证明组装，并且输入条件已明确设定。这是级别的论文证明，并非Lean语言。

[固定输入的历史段落在本阅读版省略；自然输入及完整推导见本目录三篇主文。]

P是一个真正的原始28-rowIBLP表达式: J_A0^6(A0)。它不是的替代表示法，数值比较并非仅基于顺序大小来推断的。完整的C，尤其是R，仍然保持OPEN的状态。

新成分包括：较低的开式双带风扇，严格上界定理，A(<a)<theta8六个兼容的更高类型环境，以及整体对象填充引理，该引理可以弥补低标量风扇的高度不足。下面的演员A和c不应与源A0或终点c_exit混淆。

## 1. 框架和既定输入

让j:V_lambda->V_lambda作为I3的见证，并在相同的Iter(j)中进行操作，该过程具有可应用性和有限的普通组合性。设定k0=crit(j)、k_(i+1)=j(k_i)。生成的临界点按递增顺序排列为gamma_i。应用F(G)和普通组合F o G都是DISTINCT：

~~~text
F(G)(F(t))=F(G(t)).
~~~

当演员值为t时，除非显示的F像为t，否则无法使用此公式进行读取。 将F(u)的严格上确界记作F(<t)。 u<t. 应用传输严格的最高值：

~~~text
F(G)(<F(t))=F(G(<t)).
~~~

在(p0,p1,p2)上的m线由p1=t0<...<t_m=p2和实际所有者L_i组成，具有临界点p0和L_i(p0)=t_i，还有L_i(t_i)=t_(i+1)。已建立的临界计数定理表明

~~~text
k4=gamma_(F(4)), q(5)=F(4)+1,
m-lined(k0,k1,d) => gamma_(2^m)<=d.
~~~

因此，这样的线条在k4以下结束意味着q(5)>2^m。

Hardy使用ORIGINAL Python IBLP语义，没有运行时约束条件：

~~~text
H_empty(x)=x;
H_(Q+true successor)(x)=H_Q(x+1);
H_Q(x)=H_(Q[x])(x) otherwise.
~~~

A真正的后继是最终行(0,last_index):1。A失败的复制剪切操作并未被声明为后继。这里使用的确切源锥没有失败情况。

Original definition: 所固定的原版 iblp.py（见 SOURCE_MANIFEST.json）.

以下较旧的输入被使用，并未从头进行验证：(S)、Safe-D/original-BMS 覆盖和首根替换闭包。特别地，A0[x] 由 B_(x+2)[N(x)]、N(x)=2+x(x+1)/2 覆盖；覆盖宏仅使用 0,1,x-1，而真正的源后继具有严格前缀目标覆盖。来源：

~~~text
output/iblp-01-equality-20260923/IBLP-01-no-completion-proof.zh-CN.md,
~~~

IBLP-01-BMS-upper-bound.zh-CN.md，以及本次会议的确切首根延续性和塔式证明。(B)、BMS表示无界性、前缀基本序列，以及字面种子高度路径。没有假设一般的序数与值的单调性关系。(E)表示实际情况，E/copy-tree表示参与完整频段的BMS编译器，具有备用端口，并且通过ALL隐式正边进行前置插入。

~~~text
Source: output/iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md,
~~~

见 short-terminal-initialization.zh-CN.md。适用于所有环境的备用带构造见 lift-participating-bms-spare.txt。(L) 临界点计数与同一迭代代数中的临界端点延拓；下列文献中的有限点像、严格隶属截断和严格上确界事实

~~~text
Dougherty I printed pp20--24, https://arxiv.org/pdf/math/9205202,
~~~

在Dougherty II中，端点扩展在p10中有所体现。

~~~text
https://arxiv.org/pdf/math/9503204.
~~~

以下包含了全新的cap代数、环境缝合以及数值填充处理。这个单一文件并不旨在重新证明那些较旧的基础E定理或任意的安全-D覆盖定理。

## 2. 精确的源恒等式

A0有四行

~~~text
01:1, 012:1, 0123:2, 234:1.
~~~

J_A0(Q)在A0之后，而Q被phi(0)=1重新命名，phi(i)=4+i则对应i>0。在其封闭的safe-D/J语法中，原始的完整复制规则在n>=2处给出

~~~text
J(empty)=A0;
~~~

J(Q)[n]=J(Q[n])表示非继承人，Q表示继承人。

J(Q+1)[n]=n是J(Q)的冷冻副本。

冷冻副本保留其零地址，并将正地址进行移位。特殊的原始[1]被NOT替代，用于完全复制。

原始的控制器C=A0(015):1满足C[n]=J^(n-1)(A0)和n>=2。因此，由七个四行块组成的P=C[7]=J^6(A0)也满足这些条件。重新命名与实际的+1迹测试是相容的，因为每一个非终端迹节点都是正的；没有活跃的迹进入冻结的A0背景。

对于标量 base f，定义 F_empty^(0,f)=f，在  时使用 x 次迭代得到真正的后继，否则使用原始的 [x]。在类型 r>=1 中，使用相同的规则。

但是迭代整个type-(r-1)对象，仍然选择迭代次数

并且基本索引由FINAL数值参数x控制。放置

~~~text
B_r(u)=F_A0^(r,u),       h=H_A0.
~~~

精确替换产生

~~~text
H_P(x)=B5(B4)(B3)(B2)(B1)(B0)(h)(x), x>=2.       (2.1)
~~~

这是一个高于类型的恒等式，并非某个函数的标量迭代。

## 3。实际较低的双风扇

使用演员和点位

~~~text
K=j11, b=K(j), c=K(b), d=c(K), e=d(j), f=e(K),
~~~

A=c(d), V=c(e), Q=A(K),

~~~text
mu=K(k2), theta5=K(k3), a=K(mu), c_exit=K(theta5),
theta8=j9(k3), s=j(<k1), v=K(<k2)=j10(s).
~~~

已知点顺序：k3<mu<theta5<a<c_exit<theta8<k4。此外还有crit(c)=mu、c(mu)=theta5、c(theta5)=a和c(a)=c_exit。

演员b有k2->k3->mu->theta5，所以b2=b(b)有k3->mu->theta5，并且固定了k0,k1,k2。因此D=b2(K)有

~~~text
D(k0)=k2, D(k1)=mu, D(k2)=theta5.
~~~

在(k0,k1,k2)上任意给定的m线会传输到具有共同根k2的m线，第一个点是μ，最后一个点是theta5。

在高度一处启动一个与OPEN兼容的风扇：

U=(k0,k1)，Vports=(k2,k3,mu)，正所有者K，

低所有者j3，普通截止gamma3。实际上K具有所需的三个边，j3具有k0->k2、k1->gamma3、k2->k3，而K在gamma3以下与j3具有成员关系。不需要闭合所有者。将线所有者Q_i替换为T_i=Q_i(j10)，并执行既定的前端插入变换，仅省略未使用的闭合所有者条款。经过第一步之后，最低所有者T_0(j3)已经具有旧重建的规范形式，因此每个后续的插入及其普通截止仍然有效。

让C_i表示最终的V端口点，而t_i表示当前的线锚点。C_0=t_0=mu。在第一次插入C_1=T_0(mu)=t_1时。此后

~~~text
C_(i+1)<=T_i(t_i)=Q_i(mu)<Q_i(t_i)=t_(i+1).
~~~

因此，在插入 m>=2 之后，高度 H=m+1 的上限为 C_m<theta5；对于 m=1 则允许相等。所有隐式所有者边都保持不变。

源连接器不需要闭合：R_1=id最初是空的；插入后

R'_1=id, R'_(i+1)=T_i, o, R_i。它们有

R_i(k0)=k0, R_i(k1)=U_i, R_i(k2)<=Vports_0。端点修复产生

R_i^*的最后一个等式。普通的组合K_i o R_i^*给出了(Vports_0,Vports_i,Vports_(i+1))的备用连接器。

对整个风扇应用f。 其中 f(k0)=k3， f(k1)=theta5和f(theta5)=a。 预留端口H作为闲置并使用端口0,...,H-1因为BMS有效载荷。 降低第一频带的端口1从theta5到穆； K是其带有全球像的锚点，(k2,k3,mu)。 将第二频带的端口从1降低到eta=f(K_H)(mu)。 每个正所有者都拥有SAME中间像eta： mu<theta5及其传输的共同截止值高于f(Vports_1)。 它们在f(Vports_0)处的最后一个隐边保持不变。 第二个锚点位于f(K_H)(K)位置。 这两位备用所有者分别是普通的f o R_H^*和f o (K_H o R_H^*)。 它们的三幅像是完全一致的。 由于H>=2， 那两个port-1这些改变并不会改变任何备用部件。

最终的有效载荷为B_m=(0^m)(1^m)，标量参数的接受范围分别为k3和cap<=a，而严格的范围为m>=2。因此，(E)表示自然的低标量运算。

~~~text
S(u)(m)=K_(B_m)^(0,u)(m),
~~~

其中，fast K使用2^m次迭代或BM4到[2^m]次迭代。它的标量零副本具有k2临界点，并根据需要移动数值第三源。它的高度实际上是m，而不是m*2^m。

## 4. 严格供给定理适用于所有六种类型

本部分的每个组合力都是ORDINARY组合。 在μ以下的公布近似值K~j o j，对于t<k2，则约为j^2(t)=K(t)。 因为K(t)<mu。 因此，j^2(<k2)=K(<k2)=v。

确切地 c=(K o K)(j)，因此

~~~text
c o c=(K o K)(j o j).
~~~

自K^2(k2)=a以来，严格 suprema的传输

~~~text
c^2(<a)=K^2(v).                                    (4.1)
~~~

使用K=j10(j)、j10=j9(j)，始终在真实的像参数上。

~~~text
K^2(v)=K^2(j10(s))=j10(j^2(s))=j10(K(s)).
~~~

已发表的严格sup比较结果如下

~~~text
K(s)<j10(s)<j9(s),       j(s)<k3.
Therefore
K^2(v)<j10(j9(s))=j9(j(s))<j9(k3)=theta8<k4.       (4.2)
~~~

确切地说是A=(coc)(K)，还有c^2(mu)=a。因此，A(<a)=c^2(K(<mu))。生成的临界基数μ是规则的，且K(mu)=a>mu，所以K(<mu)<a。严格递增，以及a是极限的事实，现在得出A(<a)<c^2(<a)=K^2(v)<theta8。(4.3)。特别是A(x)<theta8对于EVERYx<a，包括μ和theta5。这并不声称A(a)<k4；实际上，A(a)>k4、边界从未被使用过。

将T=j10(j3), rho=j10(gamma3)代入。下面的近似j3~j o j在gamma3处收敛到

T~K o K 在rho下方。

精确的像读数结果为T(k0)=mu、T(k2)=rho、T(mu)=a。从严格的k1<k2、T(k1)<rho开始，继续从这一严格T侧进行读数。

~~~text
gives T(k1)=K^2(k1)=theta5. Consequently
mu<theta5<rho<T(k3)<T(v)<a,                         (4.4)
~~~

使用k3<v<mu。定义Z=A(T)；它固定k0,k1，并且具有Z(k2)=A(mu)、Z(k3)=A(theta5)、Z(a)=A(rho)、Z(c_exit)=A(T(k3))。(4.5)这些是实际的A-像，而不是application/composition替代。(4.5)中的每个A-参数都是<a，因此(4.3)通过theta8来限制它们。

## 5. 六个实际的全对象环境，涉及不同领域

每一行都传输了SAME低开扇。实际的数值基数仍然是(k0,k1,k2)。更高的辅助基数则是不同的来源。

级别 环境  辅助工具      剩余第一个有效载荷  关闭输出 0    标识            k2            k3                   a

~~~text
1    V             k3           a                    c_exit
~~~

2    Q             a            c_exit               A(mu) 3    Q o V         c_exit       A(mu)                A(theta5) 4    Z             A(mu)        A(theta5)            A(rho) 5    Z o V         A(theta5)    A(rho)               A(T(k3)) 6    Z o Q         A(rho)       A(T(k3))             theta8

第一个V值是V(k2)=k3、V(k3)=a、V(a)=c_exit。Q值是Q(k2)=a、Q(k3)=c_exit、Q(a)=A(mu)、Q(c_exit)=A(theta5)。它们由A(k0)=k2、A(k1)=k3、A(k2)=a、A(k3)=c_exit以及相应的K值推导而来。接着是3和5行，通过普通的复合运算得到。4行是(4.5)。6行具有上述的前两个值。其危险的CLOSED值并未使用。取而代之的是Q(<a)=A(v)，因此(Z、o、Q)(<a)<=Z(Q(<a))=Z(A(v))=A(T(v))<theta8。(5.1)。第一个关系是故意设定的不等式：普通的复合运算不必与严格的上确界连续交换。每个特定的源上限x<a都满足Q(x)<A(v)，因此也满足Z(Q(x))<A(T(v))。

初始化器所需的严格实际界限。

对于水平>=1，通常的二维标量f0(m)=m*2^m在ag(m)-line处从真实的m线提供k3。将其端点延伸到行的辅助线，并驱动其传输的低风扇。这不需要所提供的见证的逆像。它提供载荷B_g(m)，而g(m)>=2则使源盖STRICTLY<a，许可在(5.1)中的开口。

这是全型接缝检查。 每个辅助工具都正是前一级的新参数输入。 其第一个剩余的有效载荷正是前一级选定的输出。 A辅助锚点有图片(helper,left,port1)。 在较小的numerical/lower源代码中阅读，并修复最后的像到右侧端点； 在修复之前，严格单调性表明该像的值低于port1。 零演员具有关键点的辅助功能。 因此，固定了ALL下的域坐标。 但会将当前的录取情况移动到前一个整体结果终点。 因此，每一个被复制的预言确实都接受了它的论点。 非零备用演员存在

在坐标点处，所有坐标点上的载荷剩余量达到临界点。

域坐标严格有序，即k3<a<c_exit<A(mu)<A(theta5)<A(rho)<A(T(k3))<theta8。没有不相交的Qi走廊被误认为是重叠的域。因此，通用E/full-band编译器在接收ALL输入、参数和外部环境量词的情况下，能够执行相应的操作。

~~~text
D_r(u)(...)(x)=K_(B_(g(x)))^(r,u)(...)(x), 1<=r<=6.
~~~

这是整体对角合同， 不仅仅为某个特定任务选择的矩阵x. 特别是，D6(D5)(D4)(D3)(D2)(D1)(S)(f0)是一个实际存在的合法程序，其输出行在theta8<k4处结束。

## 6. 尾部局部数值比较，包括低标量填充

让X0由非递减的f(x)>=x+1组成。更高类型的操作符具有保持每个下尾预序的特性。关系<=_b表示在ALL最终输入>=b以及所有被接纳的参数之间进行比较。混合单调性和有限迭代可以保持这种关系。最初仅在x>=2定义的源对象可以在1无损害地扩展；它们的比较在这里仅用于下尾>=3。

在BMS上的良基归纳，适用于每一个基础、论证和输入，能够快速实现input/base的单调性和强前缀特性：中正确的前缀的整个值可以迭代2^x次，而较长的矩阵值则不会受到影响。具有特定指数的<=2^x下降也无法增加固定输入值。在固定x之后，会选择源限覆盖宏；迭代过程中使用的归纳假设保持普遍量化。因此，不会使用单一输入不等式，就像它本身就是整体函数不等式一样。

将N(x)=2+x(x+1)/2和y=x+2^x-1分别赋值为0和1。对于x>=3、y>=N(x)+1，

~~~text
S(S(u))(x)>=[S(u)]^[2^x](x)>=S(u)(y)
~~~

> =G_(B_(N(x)+1))^u(N(x)).

最后一步是一个明确的种子高度路径加上输入的单调性。因此，安全-D覆盖提供了

~~~text
B0<=_3 S^2,       h<=_3 S^2(f0).                    (6.1)
~~~

对于r>=1、N(x)<=2^x和g(x)-1>=x+2。 literal路径B_H ->* R_(H-1)，仅使用0,1,2，并且相同的封面

~~~text
B_r<=_3 D_r.                                      (6.2)
~~~

这是对S的真实身高x所需的补偿。

对于每一个r>=1和ALL正输入，D_r(u)>=u^4作为整体对象。实际上，g(x)>=2；有界索引种子路径将B_g(x)简化为两个零列00。如果Z_r是那个一零列操作，那么

从2^x>=2开始，Z_r(u)>=u^2一直保持全球统一。因此

~~~text
K_00^(r,u)=Z_r(Z_r(u))>=(Z_r(u))^2>=u^4.           (6.3)
~~~

定义WHOLE运算符

Tstar=D5(D4)(D3)(D2)(D1)在X2中，

W=D6(D5)(D4)(D3)(D2)(D1)在X2中。

四重储备通过打字链下降：

~~~text
W>=Tstar^4.                                       (6.4)
~~~

从D6(D5)>=D5^4开始。在每一个后续的参数Y中，使用

~~~text
X^4(Y)>=X^2(Y)=X(X(Y))>=(X(Y))^4 when X>=power-four.
~~~

折叠后的X(Y)在下一个D_r中仍然占据主导地位，因此仍然具有四次方特性。这一过程会在有限链上不断重复。

## 7. 内部巨大的输入与q(5)的结论

~~~text
Put
~~~

U=Tstar(Tstar(S))在X1中，

qfun=U(U(f0))在X0中，

~~~text
M=qfun(1),
Y=W(S)(f0)(1).
~~~

这些都是精确的有限函数定义，并非计算得出的预言值。

由于Tstar>=D1>=power-four、Tstar(S)>=S^2和U>=Tstar(S^2)。因此，(6.1)--(6.2)的混合尾部使用是必要的。

~~~text
U>=_3 B5(B4)(B3)(B2)(B1)(B0),
~~~

并且U(f0)>=_3 h。因此

~~~text
qfun>=_3 H_P.                                     (7.1)
~~~

[固定输入的历史段落在本阅读版省略；自然输入及完整推导见本目录三篇主文。]

从(6.4)的扩展性，到Tstar>=power-four，

~~~text
W(S)>=Tstar^4(S)>=Tstar^3(S)=Tstar(U)>=U^4.
Therefore
Y>=U^4(f0)(1)>=U^3(f0)(1)=U(qfun)(1)
~~~

> =S(qfun)(1)>=qfun(qfun(1))=qfun(M)>=H_P(M).

倒数第二个不等式描述的是在输入值1时，快速空前缀强增长现象； 仅在M>=3时使用源比较。 真正的实际程序仅仅是W(S)(f0)。 其真实的初始线长度为1。 U和qfun是数值下限，分别作为物理参数提供，其未证明的端点合约为NOT。

[固定输入的历史段落在本阅读版省略；自然输入及完整推导见本目录三篇主文。]

## 8. 审计状态及未解决的主要目标

低开式风扇、四型压缩六型接缝通过根和提升剂进行了读取。严格的sup帽代数通过根、提升和Hardy代理进行了独立检查。一般的L型数值编译器通过根、提升和原始规则审核员进行了独立读取；后者检查了其源索引、全尾量词和整体对象填充，而不是外部几何基础。支持的当前文件包括：lift-low-compressed-six-type-staircase.txt、root-low-Q11-strict-cap-proof.txt、hardy-root-low-stack-numeric.txt，以及在第1节中明确命名的旧依赖项。

有界原始代码回归hardy-root-C7-certificate.py还检查了确切的路径I[0][3][0][0][1]^8[7]=J_A0^6(A0)，包括所有核心、步骤和掩码：28行、112coordinate/step字段、0.005秒。这仅检查索引，而不是符号Hardy不等式；它从不评估大型Hardy轨迹。大写字母代表5秒、100行、4000字段以及32基本步骤，整个过程已经结束。

[固定输入的历史段落在本阅读版省略；自然输入及完整推导见本目录三篇主文。]

## 附录。精确依赖关系图和可复现的小规模检查

Paths below are relative to 研究源目录.

没有output/前缀的会话文件位于

~~~text
scratch/iblp030-8h-20261015/.
~~~

对于源规则和终止条件：
- output/iblp-01-equality-20260923/IBLP-01-no-completion-proof.zh-CN.md,

section 1--2 定义为 safe D，section 3--7 证明 full-copy/cut 是闭包

并且，安静的扫描，第8部分验证了每一个A0[n]种子。
- output/iblp-01-equality-20260923/IBLP-01-BMS-upper-bound.zh-CN.md,

部分3.1--3.3定义了任意覆盖；部分4--7保持这些覆盖；部分8给出了非空严格模拟，其中方程(8.4)就是这里所使用的确切B_(n+2)[2+n(n+1)/2]覆盖。
- hardy-root-continuation-interface.txt, 第1--3节, 证明了精确性

首次根共轭与原初mark/trace条件。hardy-root-first-root-tower.txt，第1--2节阐述了语法规则；第3节则证明了在没有数值等级推理的情况下也能达到终止状态。
- hardy-root-typed-bms-bound.txt，第4节方程(4.2)是

类型提升恒等式；部分5方程(5.1)精确地等于(2.1)。

[固定输入的历史段落在本阅读版省略；自然输入及完整推导见本目录三篇主文。]

对于实际的几何形状和盖子：

~~~text
* output/iblp-laver-bms-20261013/lined-front-insertion.zh-CN.md,
~~~

headings 'Front insertion' (Chinese: 前端插入引理), the cutoff identity,

and low-owner reconstruction (统一重建下一次插入所需的低拥有者), equations

(14)--(22)，执行插入操作。在这个证明的开放版本中，只有未使用的关闭所有者被省略了。
- lift-low-open-fan-and-typed-gap.txt文件中的1--3部分证明，省略了

源连接器、所有正隐边，以及另外两条边。
- lift-participating-bms-spare.txt, 第1--5节, 提供了实际的内容

spare/root-packet编译器， 提取和端点修复； section 8记录了其有界语法回归。 其较老的部分6 '候选'定量排名论点NOT是一个额外的前提： 使用后面的lift-natural-relative-bms-oracle.txt部分 4's 对已知的 BMS 良序进行归纳， 从2--3部分获得自然全环境基础合约。 该证明不需要“幽灵所有者等级”。 在lift-mixed-base-type1-seed.txt和lift-type2-entry-relaxation.txt中开发了混合整体准入机制。 我们的精确等价性录取是后者扩大条目陈述的特例。
- root-low-Q11-strict-cap-proof.txt 给出了完整的新严格标准

代数，包括更强大的A(<a)定理。相应的实际文件为lift-low-four-type-staircase.txt，章节为1--3，以及lift-low-compressed-six-type-staircase.txt，章节为1--3。普通组合中的最大值在其最后一行是一个不等式，如(5.1)中所明确指出的那样进行了修正。

从工作区根目录中可重复执行的微小回归命令：

~~~text
python scratch/iblp030-8h-20261015/hardy-root-C7-certificate.py
python scratch/iblp030-8h-20261015/hardy-root-bms-two-band-check.py
~~~

第一个验证了原始的28-row源恒等式。 第二项检查了在高度 1..20 处的种子高度准备情况。 在最多2500步内， 五列， 21行，以及五秒保护。 这些有限的检查用于测试索引和字面宏公式； 他们做NOT证明超穷归纳法， 实际的基本嵌入， 或者巨大的数值。

[原稿快照](<hardy-root-C7-q5-single-file.txt>)
