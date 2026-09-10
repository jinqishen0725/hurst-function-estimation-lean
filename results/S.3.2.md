# Lemma S.3.2

来源：补充材料 suppdf_1.pdf，PDF 第 16 页。

## 原结论

带权相关幂双和和循环乘积在三个记忆区域的极限。

## 是否正确

原临界核中心值公式错误；一维实际短/临界极限及长记忆循环积分与谱识别已书面完成。其他维度待证。

## 修改或证明路线

S.3.24中ε4不能用|i-j|小推出f(i/N)f(j/N)≈f²(0)；应替换为f²(i/N)并求和得到∫f²。同步修正g的平方分母及Hermite rank2的2!因子。

## 已有普通数学证明（完整Lean状态另列）

普通数学：一维q=1实际短/临界带权极限与长记忆循环积分均已完成，循环积分已识别为自伴二阶混沌的谱幂和；q=2短记忆已完成。原多维全范围尚未完成。

[13_q1_short_and_critical_clt.md](../direct_proofs/13_q1_short_and_critical_clt.md)、[14_q1_long_memory_limit.md](../direct_proofs/14_q1_long_memory_limit.md)、[11_q2_mbm_short_memory_clt.md](../direct_proofs/11_q2_mbm_short_memory_clt.md)、[03_critical_variance_and_clt.md](../direct_proofs/03_critical_variance_and_clt.md)

## 已有Lean修复进度

错误结构已形式排除；替代极限待证

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.diagonal_weight_product`
- `Hurst.diagonal_not_center_value`
- `Hurst.stationaryQuadratic_translation`
- `Hurst.stationaryQuadratic_finite`
- `Hurst.centralKernel_smooth`
- `Hurst.shiftedKernel_smooth`
- `Hurst.sampled_stationary_translation`
- `Hurst.no_universal_center_value_limit`

## 尚未完成的Lean证明

文件10–14中已明确范围的一维q∈{1,2}普通数学进展尚未转Lean。仍须形式化真实Gaussian模型、协方差微分与差分、对数矩和实际权重；涉及极限的条目还需累积量、Hilbert–Schmidt算子、循环迹、二阶混沌及反演。其他维度及全边界书面证明也仍未全部完成。

依赖编号：8.2, S.3.1。

**完整原定理 Lean 证明：未完成。**
