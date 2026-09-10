# Proposition S.6.1

来源：补充材料 suppdf_1.pdf，PDF 第 36 页。

## 原结论

非规则网格差分协方差的局部g逼近和远距界。

## 是否正确

第一部分按印出的未标准化协方差是错误的；Brownian特例即可否定。

## 修改或证明路线

改为Wn(t)=σ^(-1)n^H(t) Δ^q X(t)，估计Cov(Wn(t),Wn(s))；或在原始协方差两侧恢复σ² n^(-H(t)-H(s))。

## 已有普通数学证明（完整Lean状态另列）

Brownian反例及正确协方差缩放恒等式已证明；一般非规则网格局部近似待证。

[05_normalization_and_log_moments.md](../direct_proofs/05_normalization_and_log_moments.md)

## 已有Lean修复进度

保留逐项核验记录；本轮尚未闭合本项证明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.proposition_S6_1_raw_counterexample`
- `Hurst.normalized_variance`

## 尚未完成的Lean证明

Lean反例验证的是Brownian方差1/n所对应的标量渐近命题；尚未在Lean中构造Brownian过程并实例化整条命题。修正后非规则网格的一般协方差界仍缺。

依赖编号：8.2。

**完整原定理 Lean 证明：未完成。**
