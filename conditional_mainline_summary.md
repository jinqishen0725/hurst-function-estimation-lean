# 条件 Lean 主线汇总

**验收口径更正（用户明确要求）：所有内部引理都必须完成 Lean。仅允许明确标识的外部文献引理保留为假设。因此当前主线仍未完成；第二十八阶段只是接通下游条件推导，不能计为主线验收通过。**

更新：2026-09-09，第二十八阶段。

**本阶段完成的是：把外部文献引理及已有书面证明、尚未形式化的内部支撑引理作为显式前提，接通所列一维主线。** 不是无条件完成论文，也不是声称只假设 Bardet–Surgailis Lemma 1 就已完成全部 Lean 推导。最终输入见[登记表](verification/conditional_results.json)；原 27 个编号结果的逐项判断仍见[summary.md](summary.md)及[results](results/catalog.json)。

这些前提是 theorem 的普通参数，没有新增公理或占位证明。内核检查证明的是“前提推出结论”；前提的正确性、参数适用范围及日后消除情况必须另行核对。

## 主线逐项结果

| 主要结果 | 数学判断与必要修改 | 当前 Lean 结果 | 仍使用的支撑输入 |
|---|---|---|---|
| 一维 minimax 下界，3.1 / 8.1 | 原速率保留；修复 bump、分离指标、谱/KL 归一化；含 p=1 扩展 | 已无条件完成原下界 | 无新增统计前提 |
| 实际 log 统计量的短记忆 CLT，3.3 | q=1 固定上界 b<3/4；q=2 固定 b<1；有限多项式极限须转到完整 log 函数 | `hurstHolder_stride_first_CLT_of_polynomial_limits`、`hurstHolder_grid_second_CLT_of_polynomial_limits`：实际行和和权重条件已由现有证明消除 | 有限 Hermite 多项式相关阵列 CLT；截断方差的实际极限 |
| 最优带宽的有偏极限，3.5 | G 的均值为 **−2R**，H 的均值为 **2R**；原文同写 R 不正确 | `hurstHolder_q1_conditional_raw_optimal_CLT` / q2；`hurstHolder_q1_conditional_all_scale_short_mainline` / q2：实际统计量、估计器和任意非零常尺度均已接通 | 同上；未知尺度 q2 还需尺度 L¹ 小量；q1 的该尺度小量已消除 |
| 期望偏差首项，3.4 / 4.3 相关部分 | 整数 p、额外 C^p、内部点；不能用一般 Hölder 率替代首项展开 | 已知尺度及 q1 未知尺度已有无条件版本；q2 新增 `hurstHolder_q2_unknown_scale_expected_bias_of_scale_L1`，含任意未知非零尺度 | q2 实际尺度 L¹ 小量 |
| q1 临界极限，3.3 / 3.4 | H(t)=3/4；归一化 sqrt(N/log N)；修正方差 **(9/16)∫ω²**，不能替换为核中心值 | `hurstHolder_q1_conditional_all_scale_critical_mainline`：已知/未知尺度；允许 pilot 与最终估计使用不同带宽 | 实际二阶 Hermite 项的 CLT；实际带权四阶相关双和、均值及二阶矩小量；未知尺度小量 |
| q1 长记忆极限，3.3 / 3.4 | H(t)>3/4；归一化 N^(2−2H(t))；反演后是 **−Q**，非对称极限不能丢负号 | `hurstHolder_q1_conditional_all_scale_long_mainline`；在所列带宽/矩条件下完成实际 log→逆函数→未知尺度链 | 实际二阶混沌/算子极限；带权四阶相关双和、均值及二阶矩小量；未知尺度小量 |
| 两尺度 pilot，4.1 | 使用同一有效基点，中心化为 pilot 减其自身期望；不能从两个边际 CLT 推联合结论 | `AllScalePilotMainline`：实际两尺度合并指标，有限多项式 CLT 或二阶项极限→pilot 极限；任意非零常尺度精确消去 | 合并指标上的有限多项式 CLT/方差输入；临界/长记忆使用二阶项极限及带权余项小量 |
| 所有有限 L^s 风险与 minimax | 同一固定值域类、整个 (0,1)；下界要求值域包含 1/2 邻域；原速率保留 | `q1_conditional_allfinite_minimax_mainline` / q2：对每个有限 s≥1，已知风险≤未知风险，且共同夹在常数乘 (n log²n)^(-2p/(2p+1)) 之间 | s>2 使用 **Q1RawMomentBound / Q2RawMomentBound**；它们是尚待证明的实际反演前高阶矩界，不能冒称已经从 EXT-MOM 推出 |

## 最重要的假设边界

1. **INT-CLT**：只假设有限 Hermite 多项式的相关阵列极限；完整 log 的无限展开与实际估计器极限由 Lean 证明。pilot 的输入针对合并后的两尺度统计量，保留交叉相关。
2. **INT-VAR**：实际方差及归一化小量。临界/长记忆主接口使用实际权重的双和，保留零权重；不以整张网格的粗行和冒充小窗口内的估计。
3. **INT-LONG**：实际二阶 Hermite 加权和到书面文件14的二阶混沌 Q 的极限；不假设最终 H 估计器的极限。
4. **INT-SCALE**：文件21的尺度小量。q1 短记忆最优带宽情形已经消除；q2 和其余记忆分支仍有显式输入。
5. **INT-MOM-RISK**：`Q1RawMomentBound`、`Q2RawMomentBound` 精确规定实际 `G − S − calibration(H)` 的统一高阶矩及可积性，包含所有未知非零常尺度。Lean 已证明该输入→实际非线性估计器的高阶矩→全域平方 L^s 风险→可测决策核→同类 minimax 匹配。

**INT-MOM-RISK 不是 Bardet–Surgailis 的原文引理。** 文件19从 EXT-MOM 经重复指标分组、实际相关分组、权重和 pilot/尺度误差处理推导它。这段桥接尚未形式化，归入下一阶段要补的内部支撑证明。若验收条件限定为“仅假设外部文献引理”，则不能把当前状态称为该更强目标已经完成。

## 保持的范围

- 一维；实际 harmonizable Gaussian 中点观测；固定已形式化的光滑正核。
- 风险主线：q1,p≥1,0<a≤H≤b<3/4；q2,p≥2,0<a≤H≤b<1；每个固定有限 s≥1。常数可以依赖 s。
- 精细偏差及短记忆有偏正态极限：p=r+1、C^p、固定内部位置、精确最优带宽；q2 的真值严格低于逆函数截断上界。
- 临界/长记忆：使用定理中明确列出的带宽、带权矩及尺度小量条件。基本带宽条件 δ→0、nδ→∞ **不自动保证**这些全部小量。任意带宽版本没有被声称完成。
- 高维、一般差分阶数、s=∞、非规则网格和扩展模型仍沿用原 backlog；未扩大已完成原编号结果数。

## 核验

本阶段新增 70 个数学声明；累计 1152 个数学声明及 3 个编号检查。最终构建、公理审计和逐项覆盖结果见[审计记录](verification/audit_result.json)。条件前提另由[条件登记](verification/conditional_results.json)记录；审计通过不等于前提已消除。原完整编号结果保持 **2/27**。
