from pathlib import Path
p=Path('summary.md');s=p.read_text();a=s.index('## 当前主线：');b=s.index('## 书面进度：')
new='''## 当前状态：显式支撑引理前提下的一维 Lean 主线已接通

第二十八阶段新增 **70** 条数学声明，累计 **1152** 条数学声明及 **3** 条编号检查。原文 **27/27** 个结果均有逐项文件；无条件完成的完整原编号结果仍为 **2/27：Theorem 3.1、Proposition 8.1**。构建与公理审计见[记录](verification/audit_result.json)。

按“书面证明 → 假设支撑引理的 Lean 主线 → 消除支撑引理”的顺序，现已完成中间阶段的下游推导。详细结论、适用范围和待证明输入见[条件主线汇总](conditional_mainline_summary.md)、[条件登记](verification/conditional_results.json)及[精确 Lean 前提审计](verification/conditional_boundary_audit.json)。

**这里的支撑输入包含本项目已写出、尚未形式化的内部引理。不能理解为仅假设一条外部文献定理，其余都已证明。** 特别是所有有限 Lˢ 风险在 s>2 时，仍假设实际 `Q1RawMomentBound` / `Q2RawMomentBound`；它们从 Bardet–Surgailis 矩引理的推导尚未形式化。该更强的“仅外部文献引理”目标仍未完成。

| 主线部分 | 已由 Lean 证明的链 | 留待证明的输入 |
|---|---|---|
| 一维 minimax 下界，含 p=1 | 实际 Gaussian 实验 → KL → packing → 概率/平方 Lˢ 下界 | 无新增统计前提 |
| 短记忆 CLT | 有限 Hermite 多项式 → 完整 log 统计量 → 截断反演 → 任意非零尺度的已知/未知尺度估计器 | 有限多项式 CLT、方差极限；q2 未知尺度还需尺度 L¹ 小量 |
| 最优带宽有偏极限 | 实际均值展开及带宽平衡 → G 的 −2R、H 的 2R | 同上 |
| q1 临界/长记忆 | 实际二阶项 → 完整 log → 已知/未知尺度反演；使用实际带权相关双和 | 二阶项极限、带权余项/均值/二阶矩小量、尺度小量 |
| 两尺度 pilot | 同一数据上合并两尺度指标 → pilot 极限 → 尺度精确消去 | 合并统计量的有限多项式或二阶项极限，及其方差/余项输入 |
| 全域所有有限 Lˢ minimax | 实际校准输入高阶矩 → 非线性估计器矩 → 全域平方 Lˢ 风险 → 同一参数类上下界匹配 | s>2 的实际高阶矩输入；1≤s≤2 在既定短记忆范围已无条件完成 |
| 期望偏差首项 | 已知尺度和 q1 未知尺度在所列范围已完成；q2 任意未知非零尺度的条件版本已接通 | q2 尺度 L¹ 小量 |

修正后的主要结论保留一维 minimax 速率。精细极限保留必要的符号与常数修改：G 的偏移 **−2R**，H 的偏移 **2R**；临界方差保留 **(9/16)∫ω²**；非对称长记忆极限在反演后为 **−Q**。这些修正不能概括成“仅有不影响分布的常数差异”。

范围仍为固定已形式化核、一维 q1/q2、定理明确列出的参数/带宽条件。高维、一般差分阶数、s=∞、非规则网格和扩展模型保留在 backlog。更详尽的逐项数学判断与原文修复继续见下文及 [results/catalog.json](results/catalog.json)。

下文的阶段性“尚未转 Lean / 尚未完成”描述保留历史语境，当前形式化状态以上表、[第二十八阶段](lean_batch28.md)及[条件登记](verification/conditional_results.json)为准；不改变各书面结论本身的范围。

'''
p.write_text(s[:a]+new+s[b:])
Path('mainline_status.md').write_text('''# Lean 主线状态

2026-09-09，第二十八阶段。**已完成所列一维主线在显式支撑引理前提下的下游 Lean 推导；未完成无条件主线，也未完成“仅外部文献引理作为前提”的更强版本。**

完整逐项状态见[条件主线汇总](conditional_mainline_summary.md)。每个最终条件端点的原始 Lean 陈述和源文件位置保存在[前提审计](verification/conditional_boundary_audit.json)，机器可读范围见[条件登记](verification/conditional_results.json)。

| 部分 | 状态 |
|---|---|
| 原 8.1 与 3.1 | 完整 Lean；3.1 另含 p=1 扩展 |
| 固定类、一维 q1 短记忆/q2 的全域 1≤s≤2 风险与 minimax | 已知/未知非零常尺度均已完成 |
| 实际谱特征、Gaussian KL、全域权重、偏差、短记忆协方差/MSE | 所列固定核和参数范围已完成 |
| Hermite 完备展开、实际 L² 截断、二阶项与带权四阶余项 | 已完成主线所用传递与误差界 |
| 实际短记忆 CLT 与有偏极限 | 条件链完成；INT-CLT、INT-VAR，q2 未知尺度另有 INT-SCALE |
| q1 临界/长记忆与两带宽未知尺度反演 | 条件链完成；实际二阶项极限及明确带权/尺度小量仍待证明 |
| 两尺度 pilot | 合并指标及任意非零尺度条件极限链完成 |
| 全域每个固定有限 s≥1 的 minimax 匹配 | 条件链完成；s>2 用实际 QRawMomentBound，尚未从 EXT-MOM 形式化推出 |
| 期望偏差首项 | 已知尺度/q1 未知尺度在所列范围完成；q2 为尺度 L¹ 小量条件版本 |

下一阶段消除的支撑输入是 INT-CLT、INT-VAR、INT-LONG、INT-SCALE、INT-MOM-RISK；其中 q1 最优短记忆的 INT-SCALE 已消除。外部文献原引理 EXT-MOM 与内部实际高阶矩输入 INT-MOM-RISK 必须分开，不能合并登记为一条已发表外部定理。

总计 1152 个数学声明和 3 个编号检查，原编号无条件完成 2/27。[构建/公理审计](verification/audit_result.json)只认证内核证明，不消除定理假设。原 backlog 保持不变。
''')
p=Path('verification/dependency_plan.md');s=p.read_text();s=s.replace('| INT-SCALE |', '| INT-MOM-RISK | 文件19 §3–5的实际校准输入统一高阶矩，Lean 中为 Q1RawMomentBound / Q2RawMomentBound | 内部统计模型引理，**不是** Bardet–Surgailis 的原文引理 | 从 EXT-MOM 经重复指标分组、实际相关分组、权重/pilot/尺度界推出全域实际高阶矩；目前该桥接未形式化 |\n| INT-SCALE |')
s+='''
## 第二十八阶段验收边界

下游条件链已连接到实际已知/未知尺度估计器、两尺度 pilot、临界/长记忆反演及所有有限 Lˢ minimax。参见[最终条件端点](conditional_results.json)。不是仅以 EXT-MOM 为前提：INT-CLT、INT-VAR、INT-LONG、INT-SCALE、INT-MOM-RISK 在具体端点仍有普通假设参数。

临界/长记忆使用归一化的**实际带权四阶相关双和**，不以整张网格粗行和替代小窗口内估计。带宽 δ→0、nδ→∞ 并不单独推出余项与尺度小量。书面文件21的具体带宽到这些输入的逐项 Lean 验证属于 INT-VAR / INT-SCALE 的消除工作。

后续完成标准：从相应书面前提证明输入，应用现有端点，新增不含该输入的结论，并更新输入登记和范围；单纯把输入打包进一个更大的结构不算消除。
'''
p.write_text(s)
Path('lean_batch28.md').write_text('''# 第二十八阶段：连接显式支撑前提下的 Lean 主线

2026-09-09。新增 38 个模块、70 个数学声明；累计 1152 个数学声明及 3 个原文编号检查。

[条件主线汇总](conditional_mainline_summary.md)按主要结果列出正确性、原文修改、最终 Lean 端点及未消除输入。原编号逐项文件由登记脚本重建，覆盖 27/27；完整原结果仍为 3.1 和 8.1。

## 实现内容

- 两重极限与 L¹/L² 三角阵列近似，把有限 Hermite 多项式极限接到完整 Gaussian log 函数；实际短记忆的行和和权重界已复用已有证明。
- 实际最优带宽、均值展开和非线性截断反演接合，已知/未知任意非零尺度共用同一目标极限。G 的均值为 −2R，H 的均值为 2R。
- 实际二阶 Hermite 统计量到完整 log 的带权四阶余项证明，支持临界和长记忆的两带宽未知尺度分支；保留临界核平方积分和反演负号。
- 两尺度 pilot 使用合并指标的极限输入，保留同一数据的交叉相关；证明任意非零尺度精确消去。
- 从实际反演前高阶矩到估计器矩、空间积分、平方 Lˢ 风险、可测决策核及同类 minimax 匹配；对 s≤2 复用已有无条件上界。

## 未消除的输入

条件结果明确保留 INT-CLT、INT-VAR、INT-LONG、INT-SCALE、INT-MOM-RISK 中适用的条目。最后一项是实际 QRawMomentBound，不是外部文献原引理；EXT-MOM 到它的 Lean 桥接未完成。原文更广范围及 backlog 没有扩大为已完成。

因此这一阶段的完成口径是“所列外部及内部支撑引理成立时的下游主线”。如果只允许假设外部文献引理，则更强目标仍未完成。

## 复核

- `python3 scripts/build_catalog.py`
- `python3 scripts/check_coverage.py`
- `lake build`
- `lake env lean verification/AxiomAudit.lean`
- `python3 scripts/verify_axioms.py`
- `python3 scripts/check_conditional_boundary.py`

构建与全部声明公理检查见[审计记录](verification/audit_result.json)。13 个最终条件端点及 1 个已消除输入的前序端点的完整 Lean 陈述、行号和源文件哈希见[前提审计](verification/conditional_boundary_audit.json)。源文件普通数学假设仍需另行证明；基础公理检查不能替代这一步。
''')
for name in ['README.md','lean_roadmap.md','lean_reuse.md']:
 p=Path(name);p.write_text(p.read_text()+'\n第二十八阶段当前状态：所列外部及内部支撑前提下的一维下游 Lean 主线已接通，见[汇总](conditional_mainline_summary.md)。仅假设外部文献原引理的更强版本仍未完成，尤其 EXT-MOM→实际 QRawMomentBound 的桥接；最新状态以[条件登记](verification/conditional_results.json)为准。\n')
