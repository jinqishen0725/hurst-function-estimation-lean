# 第二十八阶段：连接显式支撑前提下的 Lean 主线

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
