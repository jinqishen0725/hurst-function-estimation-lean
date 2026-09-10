# 第二十六阶段：随机反演余项与分布极限传递

新增11条数学定理，累计1065条数学定理及3条编号检查；完整原编号结果仍为2/27。主线未完成。

第二十五阶段已证明期望偏差。本批进一步处理随机变量本身。沿用其中固定内部位置、整数p和额外C^p、精确最优带宽δₙ的条件，记Gₙ为实际加权对数统计量，gₙ(H)为实际校准函数，ρₙ=δₙ^p。对q=1短记忆及q=2所列范围，证明

\[
\frac1{\rho_n}E\left|\widehat H_n-H+
\frac{G_n-g_n(H)}{2\log n}\right|\to0.
\]

`FirstEstimatorLinearization`和`SecondEstimatorLinearization`将通用余项界接到实际模型的均值和方差。`KnownScaleLinearization`通过真实实验的尺度变换，把L¹结论推广到任意已知σ≠0。`ActualEstimatorProbability`还证明标准尺度实际模型的相应归一化余项尾概率对每个ε>0趋于0。q=2仍要求H(t)<u<1，不能忽略截断内部条件。

这一步只需二阶矩；高阶矩引理不再是此反演步骤的依赖。由已验证的sqrt(nδₙ)log(n)ρₙ=1，它对应后续极限分布所用的归一化尺度。

`TriangularL1Transfer`从mathlib的有界Lipschitz弱收敛判据证明：即使每个n的样本空间和概率测度不同，只要Xₙ已有分布极限，Yₙ可测，且E|Yₙ−Xₙ|→0并满足所列可积性，就有Yₙ相同的分布极限。这是明确带输入收敛前提的传递定理，不是相关Gaussian阵列CLT。

本地mathlib现有`CentralLimitTheorem`的主要定理要求独立同分布，不能直接套在本文相关、变化权重的阵列上。可复用的是弱收敛判据、Markov不等式和此前的Gaussian基础。实际有限多项式CLT、方差常数、高阶矩/s>2、临界/长记忆与未知尺度精细极限仍待完成。

详细推导见[证明说明](proof_notes/random_linearization.md)。完整状态见[主线表](mainline_status.md)，审计见[记录](verification/audit_result.json)，源文件哈希及声明见[进度登记](verification/lean_formalization_progress.json)。
