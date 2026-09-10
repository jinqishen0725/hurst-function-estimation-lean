# Lemma S.5.1

来源：补充材料 suppdf_1.pdf，PDF 第 30 页。

## 原结论

尺度估计分量I1′的偏差和不同m区间的空间平均方差界。

## 是否正确

原长记忆空间平均方差界有实际反例，须补遗漏的m因子；修正版保留主要尺度速率，文件19另给短记忆空间平均的高阶矩。

## 修改或证明路线

一维远距离计数应为m^(2ψ−1)n^(−2ψ)乘滞后和。m≈1/b时直接合并权重给O(log²n·T(n))。取H=7/8、q=p=1、b=n^−1/2：实际Var(I1)≈log²n·n^−1/2，原界只有O(log²n·n^−3/4)。 后续补证见文件19/20；高阶矩外部依赖在文件19明确陈述和验证。

## 已有普通数学证明（完整Lean状态另列）

普通数学：已给实际合并权重与一般m近/远距离修正版。原一维远距离项漏m因子；常H=7/8、q=p=1、b=n^−1/2有实际方差幂阶反例。主要方法m≈1/b时正确界为O(log²n·T(n))。高维待证。 后续：普通数学：文件19把修正后的合并空间权重界接到任意有限阶中心矩，保留n尺度的平均收益。

[19_all_finite_loss_moments.md](../direct_proofs/19_all_finite_loss_moments.md)、[16_scale_spatial_average.md](../direct_proofs/16_scale_spatial_average.md)、[08_centering_and_long_memory.md](../direct_proofs/08_centering_and_long_memory.md)

## 已有Lean修复进度

 第二十阶段已证明q=2实际全域粗网格平均的对数尺度估计MSE，任意未知共同σ≠0，固定类[a,b]截断；线性方差O(log²n/n)、非线性项MSE、精确尺度等变性和全部统一常数均已核验。实现选择与原文不同，详见阶段说明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.log_estimator_decomposition`
- `Hurst.hurstHolder_q2_linearScale_variance`
- `Hurst.hurstHolder_q2_nonlinearScale_mse`
- `Hurst.hurstHolder_q2_logScale_mse_unknown_scale`

## 尚未完成的Lean证明

已知及未知共同非零常尺度、1≤s≤2的q=1,p≥1,b<3/4及q=2,p≥2,b<1全域平方Ls风险和匹配minimax已完成；匹配下界要求值域包含1/2邻域。未知尺度pilot、实际空间平均、尺度消去及最终H回代均已接通上述风险范围；未知尺度精细偏差/极限分布及原文其他范围仍缺。

依赖编号：4.1, 8.2, S.3.3, S.3.4。

**完整原定理 Lean 证明：未完成。**
