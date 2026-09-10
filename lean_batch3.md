# 第三批：宽谱KL与Gaussian–Fano下界

对应书面文件07、09、20，以及原Theorem 3.1、Proposition 8.1。本批继续形式化已有证明，未扩展高维或其他模型的数学研究范围。

## 1. 文件20的KL常数可以改善

对任意x>0，log x≤x−1及log(1/x)≤1/x−1给出

\[
0\le x-1-\log x\le x-2+x^{-1}=\frac{(x-1)^2}{x}.
\]

因此当正定矩阵A的所有特征值λᵢ≥m>0时，

\[
D(N(0,A)\|N(0,I))
\le\frac1{2m}\sum_i(\lambda_i-1)^2
=\frac1{2m}\sum_{i,k}(A-I)_{ik}^{,2}.
\]

本地Lean分别证明标量界、一般谱下界版本、m=1/4版本，以及谱平方和与实际矩阵元素平方和的等式。后一个等式通过实对称矩阵的酉对角化、迹的共轭不变性和逐元素展开得到。当前导出的矩阵元素版本专门取m=1/4：

\[
\boxed{D(N(0,A)\|N(0,I))\le2\|A-I\|_F^2.}
\]

不要求A趋于I，也不要求λᵢ有上界。文件20原来的常数4依然正确，这里的2更紧；不改变最终幂次或对数速率。代码：[GaussianKLBound](Hurst/GaussianKLBound.lean)。

## 2. Fano及其概率基础已移植并验证

复用StatLean固定提交`855b6afb69fead1bef066111732ed44df181040e`中的以下部分，并在本项目Lean/mathlib v4.31.0编译、公理审计：

| 本地模块 | 实际内容 |
|---|---|
| [FanoDefs](Hurst/FanoDefs.lean) | 基于mathlib的Markov模型、随机化估计量、minimax风险、均匀先验和多分类检验风险定义 |
| [EstimationToTesting](Hurst/EstimationToTesting.lean) | 可测最近点分类器、有限子族归约及分离距离带来的风险下界 |
| [KLMixture](Hurst/KLMixture.lean) | 混合分布使平均KL最小；从原KLDivergence文件选取所需部分 |
| [MutualInformation](Hurst/MutualInformation.lean) | 平均KL形式的互信息、混合分布身份及相关界 |
| [FanoLowerBound](Hurst/FanoLowerBound.lean) | 连续观测的Fano不等式及其minimax后果 |

本地[GaussianFano](Hurst/GaussianFano.lean)进一步证明互信息不超过对任意共同参考分布的平均KL，避免要求候选之间两两KL均小。

## 3. 已接成实际Gaussian有限族的下界

设M≥2，Pⱼ=N(0,Aⱼ)，每个Aⱼ正定，且

\[
\lambda_{\min}(A_j)\ge1/4,\qquad
\sum_{i,k}(A_j-I)_{ik}^2\le R.
\]

这些分布由Lean中的真实Gaussian Markov kernel实现，坐标允许相关。若目标参数两两距离至少2δ，对任意单调非负损失函数Φ，已证明

\[
\inf_{\widehat\theta}\sup_j
E_j\Phi\bigl(d(\widehat\theta,g_j)\bigr)
\ge
\Phi(\delta)\left[1-\frac{2R+\log2}{\log M}\right]_+.
\]

Lean使用扩展非负实数，减法在零处截断。风险的inf涵盖所有随机化Markov估计量。定理没有把KL、互信息或检验下界放进前提；这些都由矩阵条件推出。

`gaussian_minimax_subfamily_frobenius`还把该下界传递到包含这些候选的整个参数类。这里须提供候选所属参数类、目标分离、Gaussian law识别，以及矩阵的谱下界和元素误差界。

## 4. 与论文完整minimax的距离

已解决的基础：真实多元KL → 宽谱Frobenius界 → 参考分布互信息控制 → Fano → 参数类风险下界。

仍须形式化：

1. 实际mBm谐和特征的Hilbert空间构造、内积及真实网格协方差身份。
2. 文件09/20对这些具体矩阵的一致正谱下界和Frobenius阶估计；一般矩阵不等式不能替代它们。
3. 光滑bump的跨格Hölder控制、Varshamov–Gilbert码及Lˢ分离，把候选放进原固定函数类。
4. 原观测与白化观测的可逆变换连接，以及m(n)、候选数量、任意γ和最终渐近速率的量词处理。

所以本批不是论文完整Theorem 3.1的Lean证明。27个原编号继续逐项登记，完整原结果仍为0/27。构建与公理验证记录见[build.log](verification/build.log)、[audit_result.json](verification/audit_result.json)。
