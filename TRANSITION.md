# Hurst function estimation：当前交接入口

更新：2026-09-14（America/Los_Angeles）。项目：`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`。

**长记忆 Lean 主线尚未完成。** 已有源码通过了编译和公理审计，但旧最终定理的两组前提各自不可满足。修复主证明和后续支撑已写成文件22–24，新 Lean 组合尚待实现。本文件取代旧交接中的当前状态判断。

此前1062行文档已逐字节保存为[历史交接记录](TRANSITION_history_2026-09-14.md)，包括重复内容及已撤回的 §13 “FINAL”。其中“不是 Git 仓库”“谱文件仍无法编译”“只剩 hPert”“主线完成”等表述均不得当作现状。

## 1. 接手阅读顺序

| 顺序 | Reference | 用途 |
|---|---|---|
| 1 | [独立主线审计](verification/independent_mainline_audit_2026-09-14.md) | 两个矛盾、未消除输入、验证证据及范围判断 |
| 2 | [22：修复主证明](direct_proofs/22_long_memory_repair_lean_handoff.md) | W1–W10：带宽、直接迹转移、谱、log 与 H 端点 |
| 3 | [23：谱与概率支撑](direct_proofs/23_spectral_probability_support.md) | A：谱构造；B：正负谱匹配；C：构造 Q；D：消费现有谱截断；E：矩和特征函数 |
| 4 | [24：端点与验收约束](direct_proofs/24_endpoint_and_validation_contracts.md) | 最终同律、归一化、四阶余项、真值中心、未知尺度充分条件；末尾有可直接复制的 agent 任务说明 |
| 5 | [当前汇总](summary.md)、[书面证明索引](direct_proofs/README.md) | 与其他结果的关系；旧完成表述已撤回 |
| 6 | [API 核对文件](verification/LongMemoryHandoffAPICheck.lean)、[旧前提 Lean 反证](verification/CapstonePremiseAudit.lean) | 可重跑的接口与非空性证据 |

**验收规则：所有内部支撑引理必须完成 Lean。** 只有精确引用、完整陈述且已证明适用的外部文献定理可以作为保留前提。文件22–24中的新书面证明不是外部公理，不能作为尚未证明的最终参数。

## 2. Git、工具链与当前验证快照

- 分支 `main`；本次检查 HEAD：`9ba36f6fac79853fb6ed036a5c34523cea1e6fcb`。提交标题声称完成，该数学判断已被审计撤回。
- 早期回滚点：`checkpoint-2026-09-10-mainline-transition` → `c2d858531ad13b8819fda844cc0d71821842c9db`。正常接手不需要回滚，应保留之后可复用的成果。
- 工具链：[lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json)，Lean/mathlib 固定 v4.31.0；使用 `/Users/jinqishen/.elan/bin/lake`。
- 聚合入口：[Hurst.lean](Hurst.lean)。单文件编译不代替最终集成。
- 最新交接材料仍在工作区，尚未提交：文件22–24、独立审计、两份检查 Lean、更新的 TRANSITION/归档、summary 和证明索引。先执行 `git status --short` 核对实时状态，不要清理这些未跟踪文件。本轮未修改 `Hurst/*.lean`，未创建 Git 提交。

| 验证 | 已有证据 | 不代表什么 |
|---|---|---|
| HEAD 聚合构建 | 独立审计通过，9126 jobs | 不证明定理前提可满足 |
| HEAD 公理审计 | 2243个登记声明，未见 `sorryAx` 或自定义公理 | 不证明内部条件已消除；数量不是论文完成率 |
| 旧前提反证 | `CapstonePremiseAudit.lean` 独立编译通过 | 不证明新的替代端点已完成 |
| 新交接 API | `LongMemoryHandoffAPICheck.lean` 的16个 `#check` 通过 | 只确认接口存在，未验证新组合 |
| 文件22–24 | 书面证明及接口设计已完成 | 新谱构造、匹配桥、实际端点仍待 Lean |

独立日志：`/tmp/hurst-audit-build-2026-09-14.log`、`/tmp/hurst-audit-axioms-2026-09-14.log`、`/tmp/hurst-long-memory-handoff-api-check.log`。临时日志可能被系统清理，以下可重跑命令比路径本身更重要。

[internal_input_inventory.json](verification/internal_input_inventory.json) 仍保留旧 `mainline_complete: true` 与 INT-LONG discharged 标记，**与审计冲突，不能用作完成证据**。[check_internal_inputs.py](scripts/check_internal_inputs.py) 只检查登记一致性，不检查前提可满足性。开始修复时应按实际范围同步状态；正式验收前不得再次宣告完成。

## 3. 已确认的问题与选定路线

旧端点在 [ActualSecondChaosComplete.lean](Hurst/ActualSecondChaosComplete.lean)：`actualQ1LongStatistic_tendsto_secondChaos_complete`。

1. `hcard : ∀ n, 0 < activeCard n` 不可能成立，n=0、n=1 时活动集为空。改成由 nδ→∞ 推出的最终非空，特征非退化也只需最终成立。
2. `γ < 4h−3` 与 `4b+1−4h < γ(5−4h)` 在 h≤b<1 下矛盾。必须更换分析路径，不能只删前提后继续调用旧定理。
3. `hRiesz`、`hQ` 是需构造的谱和律，不是普通模型数据；`hwnn` 只覆盖非负权重特例。
4. 二次统计量极限不自动等于最终 H、真值中心、未知尺度或联合 pilot 的结论。

文件22的直接路线：

```text
普通模型 + 可行带宽
 → 最终几何、非退化、截断和尾包络
 → ‖实际矩阵 − Riesz矩阵‖F → 0 + 两侧范数有界
 → 每个 k≥2 的迹差 → 0（无矩阵维数损失）
 → 实际全部谱幂和 → Riesz循环积分
 → 构造的有符号谱 + Gaussian级数律
 → 实际二阶项 → log统计量 → H估计器
```

设 h=f(t)>3/4、ψ=2−2h，δ=n^(−γ)。基本带宽条件为 `0 < γ < 1`、`(1−γ)ψ < 2−2b`，对任意 h≤b<1 区间非空。截断指数另取 `θ=(1−2ψ)/2`，不要混淆 θ 与 γ。无需旧 `hPert`、`hFrozenPert`、`hγcut`、`hγdec`。

关键估计已存在：`|tr(A^k)−tr(T^k)| ≤ k C^(k−1) ‖A−T‖F`，k≥2。优先直接组合它，不继续投入冻结矩阵路线更强的维数加权误差。

## 4. Lean 源码 reference 地图

每行配合文件22–24中的具体证明阅读；存在接口不等于适配已经完成。

| 层 | 源码 | 重点 |
|---|---|---|
| 带宽、截断 | [ActualSecondChaosComplete](Hurst/ActualSecondChaosComplete.lean) | 只复用独立标量引理：`poly_cutoff_satisfiable`、`secondChaosTailFreePart_tendsto_zero_powBandwidth` |
| 活动窗 | [ActiveWindowGeometry](Hurst/ActiveWindowGeometry.lean)、[LocalWeightSupport](Hurst/LocalWeightSupport.lean) | 最终 card>0、card/S→2、活动下标 |
| 权重 | [ActiveWeightProfile](Hurst/ActiveWeightProfile.lean)、[EquivalentKernel](Hurst/EquivalentKernel.lean) | u=S·w→ω、界、连续性、常数再现 |
| 非退化 | [FirstStrideGrid](Hurst/FirstStrideGrid.lean)、[FirstStrideLongRows](Hurst/FirstStrideLongRows.lean) | 实际协方差和冻结单位方差给范数下界 |
| 尾误差 | [ActualFirstLongHilbertSchmidt](Hurst/ActualFirstLongHilbertSchmidt.lean) | `hurstHolder_q1_active_scaled_actual_tail_error_le_envelope` |
| 无权能量 | [ActualFirstLongHilbertSchmidtClosed](Hurst/ActualFirstLongHilbertSchmidtClosed.lean) | `hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed` |
| 带权能量 | [ActualFirstLongWeightedKernel](Hurst/ActualFirstLongWeightedKernel.lean) | 实际有符号权重核的能量收敛 |
| Frobenius | [ActualQuadratureConfluence](Hurst/ActualQuadratureConfluence.lean) | `actualQ1_meshEnergy_tendsto_zero`、`actualQ1_frobenius_norm_tendsto_zero`、`actualQ1UniformFrobeniusBound_of_bounded` |
| Riesz 能量 | [FirstLongRieszEnergy](Hurst/FirstLongRieszEnergy.lean) | `rankRieszKernel_energy_le_const` |
| 尖锐迹界 | [FarWordAssembly](Hurst/FarWordAssembly.lean) | `Hurst.abs_trace_pow_sub_le_frob`；非对称矩阵也适用 |
| 循环求积 | [RieszQuadratureInstance](Hurst/RieszQuadratureInstance.lean)、[DiscreteRieszCycleBridge](Hurst/DiscreteRieszCycleBridge.lean) | 求积实例、`weightedRieszDiscrete_trace_pow_tendsto` |
| 实际有限谱 | [FiniteHermitianTracePowers](Hurst/FiniteHermitianTracePowers.lean)、[FeatureQuadraticSpectral](Hurst/FeatureQuadraticSpectral.lean) | 迹/谱幂和、实际二次型同律 |
| 谱和律定义 | [ExternalSecondChaosLimit](Hurst/ExternalSecondChaosLimit.lean) | `IsWeightedRieszSpectrum`、`IsSecondChaosSeriesLaw`；文件名不赋予外部假设资格 |
| 正负排序 | [SpectralMatchingSort](Hurst/SpectralMatchingSort.lean) | 对正、负部分分别使用 `decreasingSpectralPerm` |
| 平方和尾界 | [SpectralMatchingTail](Hurst/SpectralMatchingTail.lean) | `spectralTailBound_of_padded_coefficient_convergence` |
| 有限谱排列 | [SpectralPermutation](Hurst/SpectralPermutation.lean) | 排列同律；补零另补 |
| Gaussian L² | [SecondChaosSeriesL2](Hurst/SecondChaosSeriesL2.lean) | 独立中心化平方的有限和等距公式 |
| 概率消费主接口 | [FiniteSpectralArrayConvergence](Hurst/FiniteSpectralArrayConvergence.lean) | `centeredSpectralSquares_tendsto_secondChaos_of_padded_l2` 允许有符号系数 |
| 变化样本空间 | [DistributionVaryingLawTransfer](Hurst/DistributionVaryingLawTransfer.lean)、[EventualNondegenerate](Hurst/EventualNondegenerate.lean) | 同律转移、有限坏行处理 |
| log 余项 | [FeatureQuadraticLimit](Hurst/FeatureQuadraticLimit.lean) | 二阶 Hermite 项和整个四阶起始余项 |
| 反演 | [InverseRepair](Hurst/InverseRepair.lean)、[NormalizedInverseMeasurability](Hurst/NormalizedInverseMeasurability.lean) | 截断逆、Lipschitz、可测性 |
| 未知尺度 | [FirstScaleLongL1](Hurst/FirstScaleLongL1.lean)、[FirstScaleLongRates](Hurst/FirstScaleLongRates.lean)、[FirstScaleEquivariance](Hurst/FirstScaleEquivariance.lean) | 文件24 E6–E8；当前粗行界的保守速率 |

通用 mathlib 支撑的精确名称见文件23 F，[API核对文件](verification/LongMemoryHandoffAPICheck.lean)集中展示 import 与 `#check`。文件23 A3给出主线所需的专用 HS 工具证明，不必先重建完整 Schatten 或迹类算子库。

## 5. 实施包与交付要求

| 包 | 书面 reference | 实际 Lean 交付 |
|---|---|---|
| P1 | 文件22 W1–W5 | 可满足带宽下实际全部谱幂和→J_k；无维数加权扰动/全行非空假设 |
| P2 | 文件23 A1–A6 | 构造 λ，平方可和与全部循环积分 HasSum；无预设 hRiesz |
| P3 | 文件23 B1–B5、D1 | 正负分别排序、交错补零、系数收敛、尾界、补零同律 |
| P4 | 文件23 C1–C4、D2–D3 | 构造概率空间及完整 hQ，消费谱截断得到实际二阶项极限 |
| P5 | 文件22 W8–W9、文件24 E1–E5 | 实际 log、已知尺度 H 的期望中心极限；真值中心另核偏差条件 |
| P6 | 文件23 E1–E3 | 非退化、四阶矩与非 Gaussian、全实轴特征函数及局部级数范围 |
| P7 | 文件24 E6–E8 | 可选未知尺度端点：实际尺度 L¹ 界及相同归一化下的小量 |

先完成 P1，再补构造与消费。文件24末尾有完整可复制任务说明。建议新建独立模块，保留旧代码供比较；文件22–24中的建议文件/定理名尚未创建，不能当作现有 API。

若当前用户/环境允许并行，可把 P2算子构造、P3确定性匹配、P4 Gaussian级数构造分到不同新文件；先约定接口，不同时修改公共端点或运行多个聚合构建。本文件本身不是启动其他 agent 的授权，也不能从历史 agent 名单推断它们当前仍运行。

每包报告：实际定理名、完整剩余前提、单文件编译、集成状态、公理依赖、适用性检查。编译通过和实际模型端点完成分别验收。

## 6. 后续范围与其他工作

- 文件22主证明：一维 q1、固定内部点、h>3/4、有符号权重、已知尺度期望中心；H极限为 **−Q**。
- 真值中心：文件24 E5还需 `(1−γ)ψ < γs`，s来自已证明的偏差率。任意多项式次数不能直接取 s=p，保守可取 s=1。
- 未知尺度：文件24使用实际 q1尺度估计器、pilot带宽 n^(−1/2)、平均中心数 ceil(sqrt n)，给出充分条件 `1−(1−b)/ψ < γ < 1`。仍待新 Lean 拼接，不是所有带宽版本。
- 短记忆：[ActualActiveBSCLT](Hurst/ActualActiveBSCLT.lean)、[JoinedPilotActualMarginal](Hurst/JoinedPilotActualMarginal.lean)有实质可复用成果；长记忆旧端点空真不否定这些工作，但边际桥不等于完整联合向量 CLT。
- 原编号范围和 backlog 分别核对，本轮不扩张到高维、一般差分阶数、完整 minimax 或其他已推迟范围。

## 7. 其他资料与来源

| 资料 | Reference |
|---|---|
| 原文及补充 | [正文PDF](19-AOS1825.pdf)、[补充PDF](suppdf_1.pdf)、[正文文本](source/paper.txt)、[补充文本](source/supplement.txt)、[来源哈希](verification/source_manifest.json) |
| 旧长记忆构造 | [文件14](direct_proofs/14_q1_long_memory_limit.md)；矩阵拼接及带宽按22–24修订 |
| 早期相关证明 | [文件08](direct_proofs/08_centering_and_long_memory.md)、[文件12](direct_proofs/12_q1_mbm_covariance_mse.md)、[文件13](direct_proofs/13_q1_short_and_critical_clt.md) |
| pilot/尺度 | [文件15](direct_proofs/15_two_scale_pilot.md)、[文件16](direct_proofs/16_scale_spatial_average.md)、[文件17](direct_proofs/17_unknown_scale_backfitting.md)、[文件21](direct_proofs/21_unknown_scale_fine_limits.md)；书面范围不等于现成 Lean 端点 |
| 逐编号结论 | [results/catalog.json](results/catalog.json)、[results目录](results)、[summary.md](summary.md) |
| 推迟事项 | [backlog.md](backlog.md) |
| 统计 Lean 复用 | [lean_reuse.md](lean_reuse.md)、[复用清单](verification/lean_reuse_inventory.json)、[本地StatLean](third_party/StatLean)；核对版本、许可证及前提 |
| 旧协作规范 | [lean_agent_protocol.md](verification/lean_agent_protocol.md)、[parallel_wave_prompts.md](verification/parallel_wave_prompts.md)；旧任务可能过期，按本文件分工 |
| 旧条件登记 | [conditional_mainline_summary.md](conditional_mainline_summary.md)、[conditional_results.json](verification/conditional_results.json)、[conditional_boundary_audit.json](verification/conditional_boundary_audit.json)；仅作历史边界索引 |

外部来源沿用历史记录：Bardet–Surgailis [arXiv记录](https://arxiv.org/abs/1104.4732)、[全文HTML](https://arxiv.org/html/1104.4732)；补充引用的 Taqqu [出版社页面](https://link.springer.com/article/10.1007/BF00532868)。本轮未重新联网核验这些链接。保留任何外部假设前必须匹配原文定理和全部条件；不能把“follow Proposition 6.1”变成实际统计量收敛黑箱。

## 8. 工具与验证命令

先读取实时状态，再按需运行检查：

```sh
cd /Users/jinqishen/repo/lean_verification/hurst_function_estimation
git status --short
git log -1 --oneline
rg -n 'actualQ1_meshEnergy_tendsto_zero|abs_trace_pow_sub_le_frob' Hurst
/Users/jinqishen/.elan/bin/lake env lean verification/LongMemoryHandoffAPICheck.lean
/Users/jinqishen/.elan/bin/lake env lean verification/CapstonePremiseAudit.lean
```

单模块验证先于聚合。以下为现有模块示例，新模块替换为实际名称：

```sh
/Users/jinqishen/.elan/bin/lake build Hurst.FiniteSpectralArrayConvergence
/Users/jinqishen/.elan/bin/lake env lean Hurst/FiniteSpectralArrayConvergence.lean
git diff --check
```

缺 `.olean` 先构建导入模块，不据此判断数学错误。`#check` 看接口、`#print` 看完整陈述、`#print axioms` 看依赖。读取和搜索可批量并行；依赖构建、修改、全套审计顺序执行。使用 `rg` 查声明、`apply_patch` 修改，保留其他 agent 的未提交内容。mathlib先看本地固定版本，外部定理只依据精确原文。

完成集成且源码稳定后，依次执行：

```sh
python3 scripts/check_coverage.py
/Users/jinqishen/.elan/bin/lake build Hurst > verification/build.log 2>&1
/Users/jinqishen/.elan/bin/lake env lean verification/AxiomAudit.lean > verification/axioms.log 2>&1
python3 scripts/verify_axioms.py
python3 scripts/check_internal_inputs.py
git diff --check
```

生成器会重写覆盖、公理审计和状态文件，构建/审计会覆盖正式日志；只在准备生成新快照时运行，必要时先保留旧证据。逐条检查退出码，不能只看最后一条。若新定理的命名空间/命名形式未被覆盖脚本识别，需补入审计，不能仅依赖登记数。

## 9. 完成条件与不能使用的捷径

1. 新端点能在实际模型上实例化。给出合法常数 H 的例子，并核对 h与b相距较大的可行带宽。
2. 内部 `hRiesz`、`hQ`、`hwnn`、`hNegMass`、全行 `hcard`/`hane`、`hPert` 等最终输入均已消除；内部已证明的同名局部变量没有问题。
3. 一般有符号谱使用全部 k≥2 幂和；偶数幂和不能分辨符号，平方和有界不能代替尾质量消失。
4. Q 的承载概率空间必须真实构造，不能假设任意预设空间可承载无限独立 Gaussian。
5. L² 收敛不直接给全序列 a.e. 收敛或四阶矩收敛；文件23已分别补证。
6. log/H、期望/真值中心、已知/未知尺度分别验收；边际不替代联合。
7. 单文件、聚合、覆盖、公理及逐编号范围使用同一源码快照；summary与机器登记一致。
8. 保留旧 capstone 反证，不通过删证据、忽略前提或改变模型定义来“修复”空真端点。

本次仅整理交接文档与引用；历史交接原样保留，新主线尚未开始 Lean 实现。
