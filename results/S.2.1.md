# Lemma S.2.1

来源：补充材料 suppdf_1.pdf，PDF 第 8 页。

## 原结论

声称仅在[A3]下，固定h的g(H,0,h)一致远离0。

## 是否正确

原假设不足；h=0直接反例，q=2且H→1也无统一正下界。

## 修改或证明路线

要求h≠0及H∈[γ,1-γ]；后者来自[A1]而不是[A3]。正定性+连续性+紧性才能得到一致正下界。

## 已有普通数学证明（完整Lean状态另列）

补h≠0及H紧区间后，对任意固定q的正下界已完整证明。

[05_normalization_and_log_moments.md](../direct_proofs/05_normalization_and_log_moments.md)

## 已有Lean修复进度

一维q=1/2、非零固定步长、紧Hurst区间上的修正正方差和统一下界已形式化；实际q=2常Hurst特征方差与原g一致。原文全部维度/阶数未完成。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.g_zero_direction`
- `Hurst.g_one_zero`
- `Hurst.g_two_pos`
- `Hurst.g_two_uniform_lower`
- `Hurst.featureGaussian_coordinate_variance`
- `Hurst.featureGaussian_linear_variance_pos`
- `Hurst.rawHarmonizable_memLp`
- `Hurst.harmonizableD_pos`
- `Hurst.harmonizableFeature_increment_norm_sq`
- `Hurst.g_one_two_pos`
- `Hurst.g_one_two_continuousOn`
- `Hurst.g_one_two_uniform_pos`
- `Hurst.secondDifferenceFeature_norm_sq_eq_g`

## 尚未完成的Lean证明

主线的一维q=1/2修正范围已证明。变化Hurst的Wn方差逼近仍属8.2/8.3；原文其他维度及q≥3的完整形式化未完成，不标记完整原编号结果。

依赖编号：无本项目内编号依赖。

**完整原定理 Lean 证明：未完成。**
