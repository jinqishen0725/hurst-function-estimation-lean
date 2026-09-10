# 已有Lean修复进度及影响

最新minimax下界的完整书面修复见 [文件09](direct_proofs/09_minimax_lower_bound_complete.md)，此前KL前提已补齐；Lean状态仍按下表记录。

最新普通数学证明见 [direct_proofs/README.md](direct_proofs/README.md)。本文件保留上一阶段的Lean证明范围；其中部分待证分析步骤现已有书面证明，尚未移入Lean。

2026-09-08。本文件记录修复后的数学命题、Lean 已证明的范围以及仍未完成的模型条件。完整逐项目录见 [summary.md](summary.md) 和 [results/catalog.json](results/catalog.json)。

## 当前判断

**已有可编译的替代证明；整篇论文的主要统计定理尚未全部证明。** 本轮新增46条数学证明声明。重点是把反演、误差传递、分布修正和局部多项式偏差这几个步骤接起来，不以声明数量衡量整篇论文的完成度。

| 问题／对应结果 | 已做的修复 | 对主要结论的影响 | 尚需证明 |
|---|---|---|---|
| q=1估计量缺少低端定义；3.4 | 构造双端截断逆函数，证明可测、稳定及有限样本MSE界 | 修复定义；在输入MSE成立时保留原有反演速率 | 实际对数估计量的输入MSE、精细偏差及统一性 |
| q=2非线性反演；3.4 | 在[0,u_n]截断，u_n=1−1/(n+2)；同样证明MSE界 | 增加一个不依赖未知H的截断；每个固定H<1最终在区间内 | 分布线性化余项及实际模型条件 |
| 反演负号；3.4 | 分布层面证明：Y_n+X_n→概率0、X_n⇒Z，则Y_n⇒−Z | 中心正态分布不变；非对称长记忆极限必须反射 | 论文统计量满足上述线性化关系 |
| 推论3.5均值系数 | 用概率版Slutsky定理得到N(−2R,v)、N(2R,v) | 改变偏差修正和非零均值极限；不改变这里的方差 | 输入中心CLT、归一化偏差极限 |
| 未知尺度backfitting；4.3 | 证明相关的输入和尺度误差也能传递到最终MSE | 不需要增加独立性假设；两个输入率若成立，最终率可保留 | 4.2的尺度MSE和3.2的输入MSE |
| 局部多项式偏差；8.4→3.2 | 从逆Gram矩阵直接证明精确多项式再现，并控制Taylor余项 | 可绕开旧证明的偏差求积误差；不能据旧缺口直接删除p=3/2,d=3端点 | 从本文核、网格和Hölder假设推出统一稳定性及余项；首项积分展开 |
| 临界方差；S.3.2→3.3、8.5等 | 用平移不变性形式排除普适的C·f(0)²公式 | **影响临界方差常数、标准误、置信区间**；是否保留CLT及归一化须另证 | ∫f²形式的精确极限及对应CLT |
| 下界；3.1及8.1 | 之前已修正光滑bump和部分谱估计 | 尚无证据推翻下界的幂指数，但不能认证minimax结论 | 实际协方差矩阵界、参数类packing、Fano及损失范围匹配 |

## 1. 反演：用有限样本不等式代替尾事件展开

设f在[a,b]连续、递减，且对于a≤x≤z≤b，

\[
f(x)-f(z)\ge m(z-x),\qquad m>0.
\]

定义T(y)：y在f的值域内时取逆，超出值域时取对应端点。Lean已构造T并证明

\[
|T(y)-T(w)|\le |y-w|/m,
\qquad
E(T(X)-H)^2\le\frac{\operatorname{Var}(X)+(EX-f(H))^2}{m^2}.
\]

这是任意概率空间上的有限样本定理，只需要X有二阶矩；证明同时处理T(X)的可测性和平方误差的可积性。

本文单位差分方向上，两种校准函数为

\[
f_1(H)=c-2LH,\qquad
f_2(H)=c-2LH+\log(4-2^{2H}),\quad L=\log n>0.
\]

二者的下降斜率下界均为m=2L。q=1可用[0,1]；q=2使用[0,u]、u<1以避开log项在1处的奇点。于是得到

\[
\operatorname{MSE}(\widehat H)
\le\frac{\operatorname{Var}(\widehat G)+\operatorname{Bias}(\widehat G)^2}{4\log^2n}.
\]

`boundedInverse_rate`进一步在Lean的Big-O定义下证明：输入MSE是O(R_n)，则输出MSE是O(R_n/m_n²)。序列定理把每个样本的参数区间条件写作前提；u_n最终包含固定H的结论另由`upperCutoff_eventually_contains`证明，使用时可从足够大的n开始。

对应：[InverseRepair.lean](Hurst/InverseRepair.lean)，[RateRepair.lean](Hurst/RateRepair.lean)。这已经完成非线性反演的MSE步骤，**没有把实际mBm输入的MSE率当成已证明事实**。MSE界也不能自动替代原文更精细的偏差展开。

## 2. 未知尺度：不要求两个估计量独立

令X估计f(H)+s、S估计s。Lean证明

\[
E\{T(X-S)-H\}^2
\le\frac{2}{m^2}
\left[E\{X-f(H)-s\}^2+E(S-s)^2\right].
\]

相关性不构成这个传递步骤的障碍。论文4.3剩下的关键问题是分别证明X、S的输入率，尤其4.2的空间平均协方差控制。

对应：`dependent_difference_mse`、`boundedInverse_backfitting_mse`。

## 3. 分布：保留负号并修正均值

已证明的概率命题为

\[
X_n\Rightarrow Z,\quad Y_n+X_n\xrightarrow{P}0
\ \Longrightarrow\ Y_n\Rightarrow-Z.
\]

进一步，若Z服从N(0,v)，确定性偏差B_n→−2R，且Y_n+(X_n+B_n)→概率0，则

\[
X_n+B_n\Rightarrow N(-2R,v),\qquad Y_n\Rightarrow N(2R,v).
\]

这里的收敛和高斯分布识别都是Lean概率库中的真实命题。R≠0时，新分布和原印出的N(R,v)不同也已证明。它们不证明输入中心CLT，也不证明论文估计量的线性化余项；这两个条件直接出现在定理参数中。

对应：[DistributionRepair.lean](Hurst/DistributionRepair.lean)。

## 4. 偏差：直接使用离散多项式再现

对有限设计，令

\[
M_{kl}=\sum_i K_i A_{ik}A_{il},\qquad
w_i=K_i\sum_l(M^{-1})_{0l}A_{il}.
\]

只要M可逆，已在Lean中从矩阵乘法推出

\[
\sum_i w_iA_{ik}=\delta_{k0}.
\]

因此对局部Taylor多项式P_i=Σ_kβ_k A_{ik}，若非零K_i处有|F_i−P_i|≤B，则

\[
\left|\sum_iw_iF_i-\beta_0\right|\le B\sum_i|w_i|.
\]

这允许带符号的局部多项式权重，也不会要求远离核支持的观测满足O(b^p)余项。如果逆矩阵元素有界、局部基有界且核权重总质量有界，`gramWeights_l1_bound`给出明确的L1权重界。

对−2log n·H+ell+err分别应用这个结论，得到偏差上界

\[
C\{2\log n\,B_H+B_{\ell}+\rho\}.
\]

在B_H、B_ell=O(b^p)、误差O(ρ)的条件下，即为O(log n·b^p+ρ)，**这一偏差传递步骤没有求积误差项**。因此旧证明在p=3/2,d=3留下log n的问题，可以尝试通过替换证明消除；当前尚不能声称论文全部假设已足以保证这条路线。

对应：[DirectBiasRepair.lean](Hurst/DirectBiasRepair.lean)。待补的是实际网格的统一稳定性、Hölder/Taylor界以及整数p情形的精确偏差首项。关于首项的积分区域修正仍然有效。

## 5. 临界方差：已排除错误结构，尚未证明替代CLT

对任意平稳滞后核r，定义

\[
Q(w,r)=\sum_{i,j\in\mathbb Z}w_iw_jr(i-j).
\]

Lean证明Q(w(·−k),r)=Q(w,r)，并证明有限支撑时这就是有限双和。取一个光滑紧支撑核f及其平移f(·−1/2)，它们的采样权重在偶数窗口N=2(n+1)上恰好只相差整数平移，但两个核的中心值分别为正和零。因此任何正系数C都不能使两者普遍具有C·f(0)²的归一化极限。

这是结构性反证，适用于S.3.2所使用的平稳冻结协方差形式。与论文的有限观测域对齐，可取t=1/2、N为上述偶数、观测数N²+1、带宽N/(N²+1)；核支持最终完全落在内部。该网格及实际fBm相关性的形式化连接仍未加入Lean。

候选修复依然是保留∫f²，并补齐实际ch的1/2以及Hermite系数。先前数值诊断支持该修复，但它不能替代双和极限和CLT证明。

对应：[CriticalRepair.lean](Hurst/CriticalRepair.lean)。

## 剩余工作顺序

1. 从论文真实网格与核条件推出统一Gram稳定性、Taylor界，接上3.2偏差和8.4。
2. 重建8.2协方差估计，保留有限滞后余项，处理跨临界过渡；这是上界与极限定理共同的瓶颈。
3. 证明修正后的S.3.2及三类极限定理，再验证反演线性化，接上3.3–3.5。
4. 处理未知尺度空间平均，接上4.1–4.3；独立完成KL、packing、Fano后再判断极小极大最优性。

目前可以确认若干错误改变公式和统计推断，也可以确认若干修复步骤不会额外损失收敛速度；**尚不能据此宣布文章的全部主要速率或minimax结论正确。**
