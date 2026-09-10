# 从实际权重到截断估计器的精细偏差

本说明对应第二十五阶段的54条Lean定理。以下δ表示带宽，b表示Hurst值域上端，二者不混用。原书面文件保持原样；这里明确记录实际形式化范围。

## 1. 实际权重的极限

`InteriorKernelMoments`从中点求积误差和末尾无效基点删除，证明实际核矩与积分之差≤C/(nδ)。当t∈(0,1)、δ→0、nδ→∞时，实际矩阵收敛到连续设计矩阵。后者正定已经在此前证明，故逆矩阵也收敛。`InteriorDesignLimit`将任意阶实际加权矩的极限识别为等价核矩。

`EquivalentKernel`定义ωᵣ，证明其连续、紧支撑、积分为1，且低阶矩精确再现。任意阶矩的积分表达与设计矩阵逆表达相等。

## 2. Taylor余项与实际均值

`PointwiseTaylor`直接用mathlib Taylor定理推出C^p函数的Peano余项。`LocalTaylorLeading`用实际权重的低阶矩再现消去低次项，并利用核支撑丢弃远处点；`LocalLeadingLimit`用已经证明的权重绝对和有界，推出

\[
\delta^{-p}\left(\sum_iw_iH(t_i)-H(t)\right)\to R(t).
\]

`ActualMeanResidual`使用实际谱特征对数均值误差；`GridBiasRemainderLimit`验证其在所用带宽下消失。q=2的非线性均值修正φ(H)=log(4−2^(2H))的复合正则性也有证明，除以log(n)后不贡献本阶首项。q=1固定步长修正同样消失。`OptimalMeanLeading`得到实际对数统计量的归一化均值偏差−2R(t)。

## 3. 截断反演的直接余项界

设G(x)=−mx+φ(x)+c，m>0，且G在[a,b]强递减，斜率绝对值至少m。令T(y)为实际截断反演。假设真H距两端至少d>0，φ在区间上满足|φ(z)−φ(H)|≤K|z−H|。记e=y−G(H)。

由强递减性，|T(y)−H|≤|e|/m。若没有触及截断端点，则G(T(y))=y。若发生截断，则|e|≥md，而且|y−G(T(y))|≤|e|。因此在所有情形下都有

\[
|y-G(T(y))|\le \frac{e^2}{md},\qquad
\left|T(y)-H+\frac e m\right|
\le\frac{K|e|}{m^2}+\frac{e^2}{m^2d}.
\]

这是`ClippedLinearization`对实际boundedInverse的证明。不是预先假设截断事件概率足够小。`ExpectedLinearization`和`InverseL1Linearization`使用Cauchy–Schwarz得到期望以及L¹余项界

\[
E\left|T(X)-H+\frac{X-G(H)}m\right|
\le\frac{K\sqrt{Q}}{m^2}+\frac Q{m^2d},\qquad Q=E(X-G(H))^2.
\]

取m=2log(n)、ρ=δₙ^p。真实均值与方差给出Q≤A²log²(n)ρ²；该界由`BiasVarianceScale`和`OptimalLogVariance`推出，并非额外假定实际风险结论。除以ρ后的余项至多KA/(4log(n))+A²ρ/(4d)，趋于0。由真实均值首项即得到实际估计器的期望偏差R(t)。此步骤只需要二阶矩。

`SecondEstimatorBias`与`FirstEstimatorBias`完成真实实验、实际权重、最优带宽和截断反演的连接。`KnownScaleEstimatorBias`用已证明的Gaussian推前积分身份处理任意已知非零σ。

## 4. 条件与尚未覆盖的范围

本结论要求整数p=r+1、额外C^p正则性、固定内部t及精确最优带宽。q=1使用短记忆范围b<3/4；q=2使用p≥2和b<1。q=2还要求H(t)<u<1；若H(t)=u，则d=0，上面的余项界不可用，不能据此沿用通常的未截断精细偏差或Gaussian极限。可选u>b为整个固定值域类留下余量。

本批没有证明相关阵列CLT、实际极限方差或非Gaussian极限，也没有证明未知尺度精细偏差。此前已完成的全域1≤s≤2风险并不依赖本批额外C^p条件，不应把该条件反向加到已有风险结论上。
