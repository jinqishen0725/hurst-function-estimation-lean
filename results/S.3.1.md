# Lemma S.3.1

来源：补充材料 suppdf_1.pdf，PDF 第 15 页。

## 原结论

g(H,u,h)在|u|→∞时等于(ch+o(1))|u|^(-ψ)。

## 是否正确

冻结H情形有正确Taylor证明路线；尚未完整形式化。

## 修改或证明路线

使用带1/2的ch；这里的o(1)不要错误加强为8.2(iv)的O(b log b)。

## 已有普通数学证明（完整Lean状态另列）

普通数学：一维冻结Taylor展开已证；q=1和q=2实际非恒定H的增长滞后修正版已完成。多维及一般阶数的实际模型连接待证。

[12_q1_mbm_covariance_mse.md](../direct_proofs/12_q1_mbm_covariance_mse.md)、[10_q2_mbm_mse.md](../direct_proofs/10_q2_mbm_mse.md)、[04_covariance_remainders.md](../direct_proofs/04_covariance_remainders.md)

## 已有Lean修复进度

保留逐项核验记录；本轮尚未闭合本项证明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.g_one`
- `Hurst.half_second_rpow`

## 尚未完成的Lean证明

一般q、多维以及随t变化的一致Taylor余项未证明。

依赖编号：S.2.2。

**完整原定理 Lean 证明：未完成。**
