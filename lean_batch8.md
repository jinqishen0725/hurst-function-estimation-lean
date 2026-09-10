# 第八阶段：Theorem 3.1的完整一维minimax下界

新增64条数学定理，累计416条数学定理及3条编号检查。完整原编号结果为2/27：Proposition 8.1和Theorem 3.1。完整主线仍未完成；[构建和公理审计](verification/audit_result.json)记录实际验证结果。

## 最终结论和风险范围

`theorem_3_1_minimax_liminf`证明：p≥1、M>0、任意有限1≤s<∞、0<γ<1时，存在δ>0，对任意共同非零尺度σ，实际中点观测实验满足

\[
\liminf_n\inf_{\widehat H}\sup_{H\in\mathcal H^p(M),\,0<H<1}
 P_{H,\sigma}^{(n)}\{\|\widehat H-H\|_{L^s(0,1)}>
 \delta(n\log^2n)^{-p/(2p+1)}\}>\gamma.
\]

`hurstTailRisk_eq_probability`将Lean风险定义展开为实际概率的inf/sup。决定空间包含所有在(0,1)上几乎处处强可测的实函数，Ls距离允许无穷大；决策核为关于此距离Borel结构的可测随机化估计器。因此没有用“估计器本身具有有限Ls范数”替代原风险问题。原定理p>1是此结果的直接特例；p=1利用第七阶段允许固定小Lipschitz常数的KL界。

## 已证明的链条

| 模块 | 定理数 | 作用 |
|---|---:|---|
| BumpPacking | 18 | 支撑、各阶导数统一界、跨格Hölder控制、整数p的零阶Hölder指数、同一原参数类归属 |
| BumpLoss | 14 | 点态非重叠、正bump积分、真实单位区间Ls积分与Hamming距离的精确等式 |
| CodePacking | 7 | 最大分离集及覆盖、Hamming生成函数、熵球界、指数规模码本 |
| HurstPacking | 4 | 合法光滑函数packing、实际幅度/导数界、具体候选函数的真实KL界 |
| LossGeometry | 5 | 允许无穷Ls误差的决定空间、原积分距离、参考分布Fano归约 |
| HurstExperiment | 3 | 原参数类的连续性、真实观测核、实际实验的有限样本minimax下界 |
| PackingAsymptotics | 5 | ceil取整、目标速率、对数小量、p=1仍有效的导数项/熵控制 |
| TailRisk | 4 | 严格超阈值损失、真实概率恒等式、实数Fano常数转换 |
| MinimaxLower | 4 | 固定幅度统一选择、KL/熵代数、最终eventually与原liminf量词 |

所有常数均在样本量和码字之前选定。原中点网格与首个半步长仍使用第七阶段已证明的实际KL链；没有改用冻结协方差或假设最终KL估计。

## 对论文主要结论的影响

原一维下界速率保留。必须修正原证明中的bump、排除自身的分离索引，以及谱归一化和网格处理；这些修复已纳入形式证明。不存在因p=1的固定小导数而必须损失对数速率的问题。

本阶段不把匹配上界标为完成：实际权重、变化Hurst协方差与相关对数高阶矩、未知尺度链和极限分布仍待证明。文件18/20中额外指定更窄值域的同一参数子类还需单独连接；当前完整定理对应原Theorem 3.1的0<H<1参数类。
