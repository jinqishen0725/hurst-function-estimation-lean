# 随机线性化与变化样本空间的弱极限传递

本说明对应[第二十六阶段](../lean_batch26.md)。各定理的条件在Lean声明中保留，没有把实际CLT作为已完成结果。

## 归一化随机余项

令Tₙ为实际截断反演，gₙ(h)=−2Lₙh+φ(h)+c，真H距两端至少d>0。假设Lₙ→∞、ρₙ>0且ρₙ→0，并已有

\[
Q_n=E(X_n-g_n(H))^2\le A^2L_n^2\rho_n^2.
\]

由[直接截断证明](fine_bias_and_clipping.md)，

\[
\rho_n^{-1}E\left|T_n(X_n)-H+\frac{X_n-g_n(H)}{2L_n}\right|
\le\frac{KA}{4L_n}+\frac{A^2\rho_n}{4d}\to0.
\]

`InverseL1Limit`证明此结论。`FirstEstimatorLinearization`和`SecondEstimatorLinearization`用实际模型的均值及方差推出Qₙ界，取Lₙ=log(n)、ρₙ=δₙ^p，故并未假设实际估计器的目标线性化结论。所用C^p、固定内部点、最优带宽和q=2严格内部截断条件与第二十五阶段相同。

`ScaledL1Probability`对每个n分别使用Markov不等式，得到

\[
P_n\{|R_n|/\rho_n\ge\epsilon\}
\le\frac{E|R_n|}{\epsilon\rho_n}\to0.
\]

概率空间可以随n变化。`ActualEstimatorProbability`将此结论接到实际q=1/q=2估计器；`KnownScaleLinearization`用精确Gaussian推前积分公式处理任意已知非零尺度下的L¹余项。

## 弱极限的传递

设Xₙ已经依分布收敛于Z，Yₙ可测，且差Yₙ−Xₙ最终可积、E|Yₙ−Xₙ|→0。对于任意有界Lipschitz函数F，

\[
|E F(Y_n)-E F(X_n)|\le\operatorname{Lip}(F)E|Y_n-X_n|\to0.
\]

本地mathlib的有界Lipschitz弱收敛判据遂给出Yₙ依分布收敛于Z。`TriangularL1Transfer`证明完整过程，允许Pₙ和样本空间随n变化。可积性与测试函数期望均在证明中处理。

输入Xₙ的分布收敛是明确前提。本文实际相关统计量的该前提尚待有限Hermite多项式CLT、方差极限及截断传递等步骤完成，不能把本传递定理直接登记为原文CLT。
