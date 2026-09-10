# 第五阶段：统一谱控制、差分非退化与实际中点白化

本阶段仍在完成既有书面证明；**主线尚未完成**。新增72条数学定理。范围是一维、主线q=1/2；未扩展backlog。下列结论已接入主入口，构建与公理审计记录在verification目录。

## 1. 参数控制的常数不依赖网格位置

[谱正则性](Hurst/SpectralRegularity.lean)证明每个自然数k对应的对数加权谱积分绝对可积，证明可在归一化积分下求一次参数导数，并证明D及其导数连续、D在每个[a,b]⊂(0,1)上有统一正下界。

[共同控制函数](Hurst/SpectralMajorant.lean)使用

\[
A_{a,b}(x)=\min\{|x|^{1-2b},|x|^{-1-2a}\},
\qquad a>0,\ b<1.
\]

所有自然数阶log权重乘A都可积。对a≤h≤b、|t|≤1，实际未归一化谱特征满足

\[
\|R_h(t)(x)\|^2\le4A_{a,b}(x).
\]

进一步通过点态参数微分、均值定理以及L²范数控制，证明

\[
\boxed{\exists C\ge0\quad\forall h,k\in[a,b],\ |t|\le1:
\|F_h(t)-F_k(t)\|_2\le C|h-k|.}
\]

C在所有h、k、t之外选取；不允许逐个网格点选择不同常数。这一证明直接提供文件09/20所需的参数差界。它尚未导出“归一化特征作为L²值函数具有所有所需高阶导数”的完整命题；后续混合高阶估计仍需处理。

## 2. 主线两个差分阶数的非退化性

[StationaryDifferences](Hurst/StationaryDifferences.lean)证明：对q=1或2、固定ℓ≠0及[a,b]⊂(0,1)，存在c>0，使

\[
\inf_{h\in[a,b]}g_q(h,0,\ell)\ge c.
\]

同时从实际Hilbert特征和三点Gaussian观测证明

\[
\operatorname{Var}(X(s)-2X(s+\ell)+X(s+2\ell))
=g_2(h,0,\ell)=(4-2^{2h})|\ell|^{2h},
\]

以及其对数平方的精确均值log g₂+μ₀和全部自然数阶绝对矩。这是实际**常Hurst、单位尺度**观测结论。变化Hurst的Wn方差逼近没有被当作已证明。

## 3. 文件20中的V算子界

[HurstVariation](Hurst/HurstVariation.lean)构造真实冻结项U、变化项V及完整白化特征，并证明完整特征=U+V，以及协方差的四项分解。

对于区间长度ℓᵢ>0、总长度≤1、参数变化|hᵢ−kᵢ|≤Bℓᵢ，由上面的统一参数差界得到

\[
\|V_i\|_2\le CB\sqrt{\ell_i},\qquad
\sum_i\|V_i\|_2^2\le C^2B^2,
\]

并通过有限维Cauchy–Schwarz证明

\[
\boxed{\left\|\sum_iw_iV_i\right\|_2\le CB\|w\|_2.}
\]

最终导出定理把C放在“对所有样本量n”的量词之前，没有多出n或√n因子。实际中点网格的对应版本也已证明，首项取h₀=h₁，不要求在原点观测或评价原H函数。

## 4. 原中点观测的白化是严格的分布等式

[GaussianLinearMap](Hurst/GaussianLinearMap.lean)证明任意方阵作用下，Gaussian观测的推前分布等于变换后特征的Gram Gaussian分布。证明使用实际均值与协方差的唯一性，允许原协方差奇异。另由双向数据处理证明存在可测左逆时KL不变。

[GridWhitening](Hurst/GridWhitening.lean)构造真实一阶差分矩阵。对正的区间长度，其行列式是非零对角元之积，因而可逆。第一行是X(t₁)/√ℓ₁，其余行为相邻差分。

[MidpointWhitening](Hurst/MidpointWhitening.lean)专门处理原网格

\[
t_i=(i+1/2)/n,\qquad \ell_0=1/(2n),\quad\ell_i=1/n\ (i>0).
\]

已证明网格几何、总长度≤1、不重叠区间的Brownian增量正交及白化后的Gram矩阵=I，因此

\[
\boxed{\operatorname{KL}(P_H^{(n)}\|P_{1/2}^{(n)})
=\operatorname{KL}(N(0,\operatorname{Gram}(U+V))\|N(0,I)).}
\]

这里的P是已经构造的实际单位尺度谐和Gaussian网格law，不是假设其具有所需协方差的占位对象。

## 5. 仍未完成的主线

白化等式不提供KL的n阶数。仍需冻结U的非对角/谱界、混合Q的时间与参数差分界、实际Frobenius阶估计和常尺度包装，随后接具体packing与渐近量词。上界侧的真实权重一致稳定性、变化Hurst协方差估计、相关加权高阶矩、风险速率、未知尺度传播和极限定理也仍待补齐。

本阶段没有发现新的数学错误。它形式化了已有修复的一组关键基础，不能据此宣称文章主要统计定理已完成。

截至本阶段：274条数学定理加3条编号检查，共277条声明。原27项完整状态仍为0/27；该计数包含backlog范围，因此另见[主线分项状态](mainline_status.md)，不要将声明数解释为完成百分比。20份书面证明保持原样。
