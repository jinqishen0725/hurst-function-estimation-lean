# Lemma S.3.4

来源：补充材料 suppdf_1.pdf，PDF 第 23 页。

## 原结论

联合标准Gaussian变量的Hermite正交公式 E[Hk(ξ)Hl(η)]=1{k=l} r^k k!。

## 是否正确

标准恒等式在数学上正确；完整Lean证明尚未实现。

## 修改或证明路线

τ改为η，并明确使用概率论Hermite多项式。证明：两指数生成函数的期望=e^(rst)，比较s^k t^l系数。Gaussian可积性支持求导交换。

## 已有普通数学证明（完整Lean状态另列）

联合Gaussian Hermite恒等式由生成函数完整证明，并说明L²展开的合法性。

[03_critical_variance_and_clt.md](../direct_proofs/03_critical_variance_and_clt.md)

## 已有Lean修复进度

保留逐项核验记录；本轮尚未闭合本项证明。

## Lean 对应部分

以下仅是对应的已证明片段，不是整条原文结果的证明。

- `Hurst.centered_square_covariance`

## 尚未完成的Lean证明

Gaussian生成函数、Hermite系数比较与任意k,l的形式化仍缺；当前仅有一般概率空间的二阶中心化恒等式。

依赖编号：无本项目内编号依赖。

**完整原定理 Lean 证明：未完成。**
