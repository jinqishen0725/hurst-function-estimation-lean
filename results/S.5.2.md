# Lemma S.5.2

来源：补充材料 suppdf_1.pdf，PDF 第 33 页。

## 原结论

非线性截断分量I2′的MSE及条件偏差界。

## 是否正确

一维实际pilot输入及截断非线性误差已书面证明；文件19另补所有固定有限阶矩。q=1该非线性项恒为0。

## 修改或证明路线

在原截断区间上使用log v的一、二阶导数界和投影误差；偏差控制用pilot偏差与MSE，平方误差对中心平均用Jensen，不虚构独立性收益。 后续补证见文件19/20；高阶矩外部依赖在文件19明确陈述和验证。

## 已有普通数学证明（完整Lean状态另列）

普通数学：一维q∈{1,2}实际pilot输入矩已由文件15验证，截断log v的MSE与偏差已闭合；q=1该项恒为0。高维输入仍待证。 后续：普通数学：文件19给实际截断pilot非线性误差的所有固定有限阶矩。

[19_all_finite_loss_moments.md](../direct_proofs/19_all_finite_loss_moments.md)、[16_scale_spatial_average.md](../direct_proofs/16_scale_spatial_average.md)、[08_centering_and_long_memory.md](../direct_proofs/08_centering_and_long_memory.md)

## 已有Lean修复进度

 第二十阶段已证明q=2实际全域粗网格平均的对数尺度估计MSE，任意未知共同σ≠0，固定类[a,b]截断；线性方差O(log²n/n)、非线性项MSE、精确尺度等变性和全部统一常数均已核验。实现选择与原文不同，详见阶段说明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.clip_error`
- `Hurst.log_lipschitz_from_below`
- `Hurst.hurstHolder_q2_linearScale_variance`
- `Hurst.hurstHolder_q2_nonlinearScale_mse`
- `Hurst.hurstHolder_q2_logScale_mse_unknown_scale`

## 尚未完成的Lean证明

已知及未知共同非零常尺度、1≤s≤2的q=1,p≥1,b<3/4及q=2,p≥2,b<1全域平方Ls风险和匹配minimax已完成；匹配下界要求值域包含1/2邻域。未知尺度pilot、实际空间平均、尺度消去及最终H回代均已接通上述风险范围；未知尺度精细偏差/极限分布及原文其他范围仍缺。

依赖编号：4.1, S.2.1。

**完整原定理 Lean 证明：未完成。**
