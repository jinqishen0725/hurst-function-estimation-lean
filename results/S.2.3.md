# Lemma S.2.3

来源：补充材料 suppdf_1.pdf，PDF 第 10 页。

## 原结论

协方差混合导数的全局幂界和靠近对角线时的主项展开。

## 是否正确

原q=1近对角余项有实际线性H反例；补回相对r^ψ光滑背景项后，一维q∈{1,2}内部修正版已书面证明。 文件18保留近0时x^(H(x)+H(y)-q)乘对数幂的真实背景导数界，随后在实际网格上归一化控制。

## 修改或证明路线

 新增边界与统一性修复见文件18；不修改原PDF，不把完整原结果的Lean状态改为完成。

## 已有普通数学证明（完整Lean状态另列）

普通数学：文件12给合法线性H反例，证明原q=1相对O(r log r)余项确实错误；补回r^ψ后，一维q∈{1,2}真实内部导数界与主项已闭合。其他维度待证。 后续普通数学：文件18保留近0时x^(H(x)+H(y)-q)乘对数幂的真实背景导数界，随后在实际网格上归一化控制。

[18_full_domain_l2_minimax.md](../direct_proofs/18_full_domain_l2_minimax.md)、[12_q1_mbm_covariance_mse.md](../direct_proofs/12_q1_mbm_covariance_mse.md)、[10_q2_mbm_mse.md](../direct_proofs/10_q2_mbm_mse.md)、[04_covariance_remainders.md](../direct_proofs/04_covariance_remainders.md)

## 已有Lean修复进度

 第十三阶段已完成一维q=1、固定0<a≤H≤b<3/4的实际全网格相关平方行和、O(1/(nδ))方差、精细均值，以及原Hölder类p≥1全域截断估计MSE；常数和样本门槛统一于参数类。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.half_second_rpow`
- `Hurst.kernelIncrement_mesh_parameter_bound_general`
- `Hurst.grid_mixed_covariance_bound`
- `Hurst.grid_increment_covariance_perturbation`

## 尚未完成的Lean证明

文件10–14中已明确范围的一维q∈{1,2}普通数学进展尚未转Lean。仍须形式化真实Gaussian模型、协方差微分与差分、对数矩和实际权重；涉及极限的条目还需累积量、Hilbert–Schmidt算子、循环迹、二阶混沌及反演。其他维度及全边界书面证明也仍未全部完成。 后续文件18已书面补齐明确范围的全域MSE/minimax；这些新增仍未转Lean，其余边界结论仍保留缺口。

依赖编号：S.2.2。

**完整原定理 Lean 证明：未完成。**
