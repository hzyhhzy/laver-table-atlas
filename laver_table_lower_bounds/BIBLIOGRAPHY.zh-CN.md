# 外部文献与归属 · [English](BIBLIOGRAPHY.md)

下列为证明引用的文献。作者姓名和版本按本次整理使用的原始文献记录列出。

1. **Renrui Qi, *Notes on Laver Tables*, v5.** 给出普通 BLP/BLS、有限参数的 linedness、标准五行实现、长链构造，以及临界点计数与周期之间的关系。本图谱在此基础上另行推导了标记、父包和带类型的 BMS 扩展。[文献记录](https://arxiv.org/abs/2501.06733v5) · [全文](https://arxiv.org/html/2501.06733v5)
2. **Randall Dougherty, *Critical points in an algebra of elementary embeddings*.** 本文用到其中的有限点表、成员截断代数和严格上确界比较。期刊版见 *Annals of Pure and Applied Logic* 65 (1993)。[文献记录](https://arxiv.org/abs/math/9205202) · [PDF](https://arxiv.org/pdf/math/9205202)
3. **Randall Dougherty, *Critical points in an algebra of elementary embeddings, II*.** 给出标准有限链、端点延长和临界点计数所用的结果。[文献记录](https://arxiv.org/abs/math/9503204) · [PDF](https://arxiv.org/pdf/math/9503204)
4. **Rachel Hunter, *Well-Orderedness of the Bashicu Matrix System*, v3.** 标准 BMS 的良序性及父表复制见此文，特别是引理 2.5。这里采用 arXiv 的作者署名 Rachel Hunter。非标准覆盖的定量估计及森林模拟由本图谱另证。[文献记录](https://arxiv.org/abs/2307.04606v3) · [全文](https://arxiv.org/html/2307.04606v3)
5. **Astra–Qi 的 IBLP 良基性稿。** 短尾对应采用该稿指定版本的规则。原版 Python 另有固定哈希。论文版与旧版程序各自的守卫条件按所需范围逐项核对。[作者提供的 PDF](https://github.com/QiRenrui/basic-laver-pattern/blob/main/IBLP_wellfoundedness_en.pdf)

Steel 的有界 application 定理取 Qi 论文所引的表述。短 modify 总次数所用的有限整数势函数在本地稿中证明。

## 本地版本

原始研究稿保留当时的数学表述。三篇主文给出实际调用的结论，以及把输入改为证明自然产生的参数之后的推导。

用户提供的原版 IBLP 内核按字节收录，用于固定规则版本及复算有限恒等式。保留原有联系信息和归属。第三篇主文在数学上另行定义了采用论文守卫的转移。[原版内核](code/iblp_original.py) · [源文件及哈希](SOURCE_MANIFEST.json)

这里引用的外部论文通过链接提供。随附材料为本地证明、有限核查及原始内核。
