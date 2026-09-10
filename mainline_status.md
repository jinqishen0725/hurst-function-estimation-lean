# Lean 主线状态

**验收口径更正（用户明确要求）：所有内部引理都必须完成 Lean。仅允许明确标识的外部文献引理保留为假设。因此当前主线仍未完成；第二十八阶段只是接通下游条件推导，不能计为主线验收通过。**

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
