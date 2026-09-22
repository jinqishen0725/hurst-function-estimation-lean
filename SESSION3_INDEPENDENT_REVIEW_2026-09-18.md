# Session 3 独立复核：构建通过，主线尚未完成

复核对象：`0e6adc8c3e4ecd92613070507aecbc2842afacf4`，尤其是
[新交接文档](TRANSITION_session3_2026-09-18.md)。复核开始时工作区干净。
本次只新增此报告和 [Lean 前提审查](verification/Session3PremiseAudit.lean)，不改原实现。

## 判定

**不能接受“仅余 hPos／主线已经完成”的判断。** 新增了真实的可复用 Lean 证明，
但当前谱 capstone 有不可满足的 `hconst` 前提，H 估计器最终端点还有其他不可满足前提。
这说明形式化没有证明所需的实际模型结论；不说明原论文的结论被反驳，也不说明 Lean 内核有错。

## 1. 阻断：hconst 对所有等价核阶数都不成立（已用 Lean 证明）

位置：

- [CapstoneV3Closed.lean](Hurst/CapstoneV3Closed.lean)，raw / degreeOne / antitone 三种端点，
  尤其 `actualQ1LongStatistic_tendsto_secondChaos_v3_closed_antitone`。
- [GeneralKHasSumFinal.lean](Hurst/GeneralKHasSumFinal.lean)，`HS.rieszSpectrumVal_hGen`。
- 上游 `RieszCompactEnumeration`、`P2SpectrumCloseout` 等谱构造继承同一个前提。

实际前提是

```lean
hconst : ∀ x y : ℝ,
  (HS.I : Set ℝ).indicator omega x = (HS.I : Set ℝ).indicator omega y
```

`HS.I = [-1,1]`。取 `y = 2`，右边为零；再取任意 `x ∈ HS.I`，得到 `omega x = 0`。
但已有 `Hurst.equivalentKernel_integral r` 证明了每个 `r` 的等价核在 `[-1,1]` 上积分为 1。
因此 `omega = equivalentKernel r` 时矛盾，**包括 r = 1**。

[Session3PremiseAudit.lean](verification/Session3PremiseAudit.lean) 已证明：

- `session3_indicator_const_forces_zero`
- `session3_equivalentKernel_hconst_impossible`

通用 `hGen` 的 `omega` 参数没有直接矛盾，因为零权重是可用实例；
但其当前 `hconst` 强迫区间内权重为零，所以不能实例化到需要的等价核。
补上 Hilbert 基或将 hGen 接到 capstone 不会解决这个问题。

根源是 [HSOperatorLayer2.lean](Hurst/HSOperatorLayer2.lean) 定义的核为
`omega(x) * c * |x-y|^(-psi)`（附区间 indicator），即 `W K`，一般不是自伴算子。
现有 `hconst` 用常数权重来保证对称，但量词甚至覆盖了区间外。
仅把量词限制到区间内仍不能覆盖一般非恒定等价核。

修复参考此前书面方案：

- [22：W6](direct_proofs/22_long_memory_repair_lean_handoff.md)：无权正算子 K、
  有界自伴乘法算子 W，构造 `B = K^(1/2) W K^(1/2)`。
- [23：A4–A6](direct_proofs/23_spectral_probability_support.md)：证明 B 自伴、HS，
  再证明其谱幂和等于带权循环积分。应复用新加的通用 HS／Parseval／核复合工具。

## 2. 阻断：最终 H 估计器端点仍然不可实例化

[FullChainEndpoint.lean](Hurst/FullChainEndpoint.lean) 中
`actualQ1_knownScaleH_fullChain` 及 expectationCentered / feasible 变体仍要求

```lean
hm : ∀ n, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-gamma)) t).card
```

`n = 0` 时集合为空。新审查文件已直接证明
`session3_fullChain_all_rows_impossible`。二次型层的
`actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard` 已修复该类问题，
但修复尚未传播到最终 H 估计器层。

此外，FullChainEndpoint、P5LogHLayers、P5JoinInstantiation 的 `hE2` 要求
**未归一化**相关平方总和 `sum_i sum_j rho_ij^2 ≤ C` 最终一致有界。
这是另一个数学上的不相容前提：在它们同时要求的 `hane` 下，`rho_ii = 1`，
所以总和至少为活跃点数 m_n；可行带宽下 m_n → ∞。
这条 hE2 诊断在本次报告中是直接数学推导，尚未单独写成 Lean 矛盾定理。
定义见 `Hurst/GaussianLogRisk.lean` 的 `featureCorrelation`；活跃点数发散见
`Hurst/OptimalActiveRowDensity.lean` 的 `localWeightActiveSet_card_tendsto_atTop`。

应按 [22：W8–W9](direct_proofs/22_long_memory_repair_lean_handoff.md)
使用归一化能量 `S^(2*psi-2) * sum_i sum_j rho_ij^2 = O(1)`，
结合近／远带证明四阶 Hermite 余项消失，再处理 log、clipping 和中心化。
不能只把 hE2 改成正确形状后沿用原证明，须同步修正下游估计。

## 3. 一般带符号极限仍未闭合

`CapstoneV3Closed` 的当前端点要求 `hPos` 与最终非负权重 `hwnn`。
[P3SignedMatching.lean](Hurst/P3SignedMatching.lean) 的最终匹配结果则要求
负谱平方质量 `hNegMass → 0`；文件自身也列出 interleaved sorted row 的分布认同缺口。
这些结果处理的是负谱渐消的情形，不能代表允许非零负谱的通用极限。

因此，新交接文档中“EvenPeeling 覆盖带符号区域，所以 hPos 非阻塞”的说法不成立。
偶次幂无法区别 lambda 和 -lambda。应按
[23：B–D](direct_proofs/23_spectral_probability_support.md) 完成正／负谱分别排序、
有符号系数的 l2 收敛和二阶 Gaussian chaos 的极限。

## 4. 确实取得的进展与验证范围

- 重新运行 `lake build`：**9190 jobs，成功**。
- 重新运行 `lake env lean verification/AxiomAudit.lean`：成功；注册表中
  **2522 条声明（2519 条数学证明 + 3 条索引）**全部出现在日志，
  只包含 `propext`、`Classical.choice`、`Quot.sound`。
- `P1ActualPowerSums.actualQ1_eigenPowerSums_feasible` 的实际声明已直接给出
  普通模型假设及可行带宽下、所有 k ≥ 2 的实际矩阵谱幂和极限，
  没有 hconst、旧矛盾带宽或全样本量非空前提。这是值得保留的重要进展。
- 核复合、一般链积分可积性、张量 Parseval、通用谱迹桥等提供了可复用工具。
  它们编译成立，不等于目前依赖 hconst 的 Riesz 实例可以使用。
- hTwo / hGen 的组合工作确实存在，但其到实际等价核的应用被第 1 项阻断。
- 没有逐行重审全库每个证明；本次重点是新完成声明的构建、公理依赖、最终前提和模型适用性。

审计脚本也有覆盖边界：`scripts/check_coverage.py` 跳过首个命名空间非 Hurst 的模块，
现有 AxiomAudit 没有直接列出 `HS.rieszSpectrumVal_hGen`。本次在新增审查文件中
单独 `#print axioms` 检查它、`HS.hBridge`、`HS.hPair_riesz` 和 antitone capstone。
后续应使审计注册表系统地涵盖 HS 模块；不要把 2519 当作全项目所有定理的总数。

## 5. 复现与下一步顺序

```sh
cd /Users/jinqishen/repo/lean_verification/hurst_function_estimation
/Users/jinqishen/.elan/bin/lake build
/Users/jinqishen/.elan/bin/lake env lean verification/AxiomAudit.lean
/Users/jinqishen/.elan/bin/lake env lean verification/Session3PremiseAudit.lean
```

本次日志：
`/tmp/hurst-independent-build-2026-09-18.log`、
`/tmp/hurst-independent-axioms-2026-09-18.log`、
`/tmp/hurst-session3-premise-audit-2026-09-18.log`。

建议按依赖顺序修复：

1. 更换实际谱对象，消除 hconst，证明它和已有循环积分的认同。
2. 完成一般有符号匹配；若暂时只做非负子情形，必须明确收窄结论并证明该子情形适用。
3. 把 eventual／零填充处理传播到 H 估计器层，用正确归一化能量重做 P5。
4. 消解实际 bias、nondegeneracy 等内部前提，完成 truth-centered 与 unknown-scale 组装。
5. 最终导出一个只含普通模型条件和明确允许的外部定理的端点，
   并给出具体可满足实例；再更新 summary 和 transition 的完成状态。

这不是“所有新增证明都要重写”，但也不是“只剩常数或 Hilbert 基”的收尾。
