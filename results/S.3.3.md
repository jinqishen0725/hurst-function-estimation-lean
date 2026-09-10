# Lemma S.3.3

来源：补充材料 suppdf_1.pdf，PDF 第 23 页。

## 原结论

相关幂带权双和的短、临界、长记忆三分支统一界。

## 是否正确

一维三分支方差及跨临界过渡界已书面证明；所列短记忆范围现有全域界及任意有限阶矩，外部Gaussian矩引理依赖明确列出。

## 修改或证明路线

 新增边界与统一性修复见文件18；不修改原PDF，不把完整原结果的Lean状态改为完成。 后续补证见文件19/20；高阶矩外部依赖在文件19明确陈述和验证。

## 已有普通数学证明（完整Lean状态另列）

普通数学：d=1、q=1的实际三分支方差界与跨临界过渡形式已完成；q=2实际界已完成。三分支拆开的常数仍不得声称跨临界一致；其他维度待证。 后续普通数学：文件18由全网格相关平方和证明所列一维短记忆分支的全域O((nb)^-1)方差。 后续：普通数学：文件19进一步从真实相关平方行和推出任意有限阶矩，明确标记外部Bardet–Surgailis矩引理依赖。

[19_all_finite_loss_moments.md](../direct_proofs/19_all_finite_loss_moments.md)、[18_full_domain_l2_minimax.md](../direct_proofs/18_full_domain_l2_minimax.md)、[12_q1_mbm_covariance_mse.md](../direct_proofs/12_q1_mbm_covariance_mse.md)、[10_q2_mbm_mse.md](../direct_proofs/10_q2_mbm_mse.md)、[04_covariance_remainders.md](../direct_proofs/04_covariance_remainders.md)

## 已有Lean修复进度

 第十二阶段直接从Gaussian密度重叠与正交旋转证明偶函数的相关平方协方差界，并接到实际加权统计量；无需Hermite完备性，但尚不替代任意高阶矩。 第十三阶段已完成一维q=1、固定0<a≤H≤b<3/4的实际全网格相关平方行和、O(1/(nδ))方差、精细均值，以及原Hölder类p≥1全域截断估计MSE；常数和样本门槛统一于参数类。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.short_memory_q1_d1`
- `Hurst.short_memory_q1_d2`
- `Hurst.short_memory_q1_d3`
- `Hurst.short_memory_q2`
- `Hurst.gaussian_even_covariance_bound`
- `Hurst.gaussian_log_square_covariance_bound_general`
- `Hurst.featureGaussian_log_covariance_bound`
- `Hurst.gaussianLogStatistic_variance_correlation_bound`
- `Hurst.gaussianLogStatistic_variance_row_bound`
- `Hurst.actual_grid_correlation_rows_eventually`
- `Hurst.actual_grid_local_log_variance`

## 尚未完成的Lean证明

已知及未知共同非零常尺度、1≤s≤2的q=1,p≥1,b<3/4及q=2,p≥2,b<1全域平方Ls风险和匹配minimax已完成；匹配下界要求值域包含1/2邻域。实际q=1短记忆和q=2行和、方差、最优带宽MSE及统一Hermite截断已完成。有限多项式相关阵列CLT、实际方差极限、高阶矩及s>2风险、临界/长记忆极限、未知尺度精细偏差/分布及更广带宽和非整数精细偏差范围仍缺。

依赖编号：8.2, S.2.1。

**完整原定理 Lean 证明：未完成。**
