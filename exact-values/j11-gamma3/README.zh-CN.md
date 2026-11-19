# 第 11 行第 8 列何时第一次非零？ · [English](README.md)

令 $T=2^{2048}$。在 I3 下，按自然数递增枚举生成临界点，有

$$
J_{11}(\gamma_3)=\gamma_T,\qquad
11 *_T 8=0,\qquad 11 *_{T+1} 8=2^T .
$$

这里 $A_m$ 有 $2^m$ 个元素，表项取模 $2^m$ 的余数。投影到较小阶可知，该位置在所有 $m\le T$ 的表中都是零。临界点结论对每一个 I3 见证成立，见证是 Lean 定理的显式参数。[中文纸面证明](proof.zh-CN.md) · [Lean 主定理](lean/RankSteelEndpoint.lean) · [有限表判据](lean/Gamma11Endpoint.lean)

## 证明与核验

- `j11_gamma3_exact` 证明临界点等号，`finite_table_reading_of_I3` 给出普通有限表的对应读数。集合论部分使用 Steel 定理导出首行周期无界。[I3 与临界谱的定义](lean/RankI3.lean) · [Steel 归约](lean/RankSteelReduction.lean)
- 103 个本地 Lean 模块的核验记录分为 100 个核心模块和最后 3 个 Steel 接口模块。最终定理的公理清单为 `propext`、`Classical.choice`、`Quot.sound`，I3 出现在定理的前提中。[核心重放日志](verification/check-20261118-core-final.log) · [最终重放日志](verification/check-20261118-complete-endpoint.log)
- 六个附录给出精确等号的纸面推导。另附在小表上检查位块和升阶公式的程序与结果。[有限核查程序](checks/first_four_period_audit_20261118.py) · [核查记录](checks/first_four_period_audit_20261118.json)

从源码重建时，上游 `SetLanguage` 中的两个证明需要让 `simp` 保留子类型量词，以便使用各自给出的见证。这两处写为 `simp [-Subtype.forall, Fin.snoc]`。Lean 内核已从源码重放 62 个适配依赖和 103 个本地模块。统一换行后，103 个本地模块的新日志与原始日志逐字一致。清单也保留了上游模块调整前的哈希。[完整重放日志](verification/atlas-rebuild.log) · [适配步骤](prepare_steel.py) · [源文件记录](verification/sources.json)

## 在本地检查

从本目录运行以下命令可核对源码哈希、103 个模块的重放记录和最终公理清单。此命令只需 Python 3.10 或更高版本。

```sh
python -B check.py
```

如需重新编译，使用 Lean **4.33.1**，先编译 本图谱中的共享有限表工程。另需用同一版 Lean 构建的 Mathlib，含 `Mathlib.SetTheory.ZFC.VonNeumann` 及其依赖。Mathlib 源码取提交 `eba3d887fc52c98627f4b81507c0efc3096e91b9`。Steel 源码从 FrenzyMath/LaverTable 的提交 `1f5ee8c0f6dee8fe25f8971371ff6533dca0a707` 读取。[共享工程](../../laver_table_lower_bounds/lean/README.zh-CN.md) · [Mathlib 源码](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) · [上游 Steel 定理](https://github.com/frenzymath/LaverTable/blob/1f5ee8c0f6dee8fe25f8971371ff6533dca0a707/LaverTables/Algebra/Steel.lean)

```sh
python -B ../../laver_table_lower_bounds/lean/build.py --lean-bin /path/to/lean/bin
python -B check.py --rebuild --lean-bin /path/to/lean/bin --mathlib /path/to/mathlib4 --upstream /path/to/LaverTable
```

如果 Mathlib 依赖的工作树和编译结果位于单独的 Lake 包目录，可追加 `--packages /path/to/.lake/packages`。构建程序将上游证明中固定的集合宇宙改为参数，按清单核对 62 个适配模块，再依次编译这些模块和 103 个本地模块并调用 `leanchecker`。生成物写入 `.build/`。源码清单同时记录依赖版本和两份原始日志的哈希。[源码清单](verification/sources.json) · [上游源码适配](prepare_steel.py) · [核验程序](check.py)

同一命令也可分段运行。`--part steel` 核验上游的 62 个模块，`--part core` 核验本地的 100 个核心模块。这两部分可以独立重建。二者完成后，在同一构建目录中用 `--part endpoint` 核验最后 3 个模块，得到带显式 I3 前提的等号。

[辅助演算索引](notes/README.zh-CN.md)

[返回首页](../../README.zh-CN.md)
