# Lemma S.2.2

来源：补充材料 suppdf_1.pdf，PDF 第 9 页。

## 原结论

冻结指数的最高奇异项系数为H、|h|²、方向投影的多项式。

## 是否正确

按冻结H的主项解释有正确递推路线；未完成一般阶数和多维证明。

## 修改或证明路线

明确只抽取所有导数作用在距离上的主奇异项，H导数属于余项；主文一维ch公式必须补1/2。

## 已有普通数学证明（完整Lean状态另列）

普通数学：一维冻结最高阶系数已证；q=1、q=2实际变指数主项与余项分离已由文件10/12完成。一般阶数的非恒定H及多维待证。

[12_q1_mbm_covariance_mse.md](../direct_proofs/12_q1_mbm_covariance_mse.md)、[10_q2_mbm_mse.md](../direct_proofs/10_q2_mbm_mse.md)、[04_covariance_remainders.md](../direct_proofs/04_covariance_remainders.md)

## 已有Lean修复进度

保留逐项核验记录；本轮尚未闭合本项证明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.second_rpow_derivative`
- `Hurst.half_second_rpow`

## 尚未完成的Lean证明

一般q方向导数递推和带H导数的全部余项分离未形式化。

依赖编号：无本项目内编号依赖。

**完整原定理 Lean 证明：未完成。**
