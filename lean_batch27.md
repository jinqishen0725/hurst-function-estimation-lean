# 第二十七阶段：先书面补齐，再完成带前提的Lean链

新增17条内核可检查的数学声明，累计1082条及3条编号检查。声明中包括显式前提的条件定理；完整原编号结果仍为2/27。条件主线本身也尚未全部接通，不能据此宣布已经进入最后的外部引理证明阶段。

## 新书面证明

[文件21](direct_proofs/21_unknown_scale_fine_limits.md)补齐之前笼统标为“未知尺度精细极限”的明确范围。它发现并利用实际均值中−2L乘平滑H与2L乘pilot的抵消，再对截断非线性项作一次Taylor展开。线性随机部分使用真实合并权重，二次余项只用pilot二阶矩，得到改进尺度L¹误差界。

由此，短记忆同阶最优带宽下未知尺度估计器与已知尺度参照具有相同偏差首项和Gaussian极限。另给临界/长记忆一组明确满足小量条件的欠平滑带宽版本；没有宣称任意带宽都有相同极限。原3.5要求整数p，因此非整数普遍首项不计为该原定理的缺口。

## Lean中实际完成的连接

`OracleScaleL1`证明实际截断反演受到尺度误差扰动时的L¹界，以及归一化L¹收敛。`OracleScaleBias`和`OracleScaleDistribution`分别传递期望首项与分布极限，允许每个n有不同样本空间，不要求两项误差独立。

`ActualScaleIntegrability`从实际两尺度Gaussian特征推出尺度估计器最终属于L²。因此实际偏差定理不把尺度可积性留作额外统计输入。

`FirstUnknownConditionalBias`和`SecondUnknownConditionalBias`接到真正的q=1/q=2估计器、原函数类、最优带宽、实际概率测度和此前已证明的已知尺度偏差。唯一新的统计小量前提是E|尺度误差|/(log(n)δₙ^p)→0。

其中q=1前提已由`FirstScaleNegligible`消除：复用之前已证明的E(尺度误差)²/log²(n)≤C/n，结合nδₙ^(2p)→∞及Cauchy–Schwarz即可。`FirstUnknownFineBias`给出单位真实尺度实验的实际未知尺度估计器偏差首项，`FirstUnknownScaleTests`和`FirstUnknownAllScaleBias`再用真实实验的精确尺度不变性推广到任意未知σ≠0。

这个已完成结论要求固定0<a≤H≤b<3/4、整数p=r+1≥1、额外C^p、固定内部t以及精确最优带宽。q=2使用更宽的pilot截断[a/2,u]且b<u<1，目前仍依赖文件21的尺度L¹小量前提。

`ActualUnknownConditionalLimits`给实际q=1/q=2估计器的条件分布极限传递。它仍要求已知尺度参照的实际分布极限和尺度小量；前者将由INT-CLT/INT-VAR等输入链提供，不能把本定理本身视为实际相关阵列CLT。

## 前提追踪与剩余顺序

[条件登记](verification/conditional_results.json)区分待证明输入和已经消除的输入，[依赖表](verification/dependency_plan.md)区分真正外部的Bardet–Surgailis矩引理与项目内已有书面证明的CLT、方差、长记忆和尺度界。全量公理审计仍进行，但审计通过不等于前提已经消除。

接下来仍需先完成其余条件性Lean链：实际对数CLT/方差、临界长记忆、所有有限s风险，以及未知尺度其余已书面明确的范围；然后再集中补这些延后输入的Lean证明。新顺序不允许把待证明结论变成自定义公理，也不允许把条件性结果登记为完整原定理。
