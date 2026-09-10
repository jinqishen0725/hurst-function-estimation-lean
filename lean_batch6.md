# 第六阶段：冻结矩阵与真实谱下界

新增39条数学定理：FrozenEstimates 25条、MatrixEstimates 12条、GaussianScale 2条。累计313条数学定理和3条编号检查。主线未完成；完整原结果仍为0/27。

## 对应文件09、20的实际证明

对中点观测网格，第一段长度1/(2n)，其余为1/n。以a控制H偏离1/2的幅度，B控制离散Lipschitz常数，要求H值域在[1/4,3/4]，a log(2n)≤1。

- 冻结增量的对角误差≤2 exp(2) a log(2n)。
- 非相邻协方差通过两次空间中值估计保留h+k−1因子；相邻项通过指数参数中值估计及精确尺度公式处理。合并得到所有i≠j的绝对协方差≤K a/|j−i|，K独立于n、H。
- 复用mathlib调和数界，得到每行绝对误差和≤C a(1+log(2n))。再由实际矩阵二次型和行和证明冻结Frobenius平方≤n[C a(1+log(2n))]²。
- 若C a(1+log(2n))≤7/16，则冻结线性组合范数≥3/4乘系数范数。结合上一阶段实际V算子界和D B≤1/4，得到完整白化特征Gram正定且所有特征值≥1/4。
- 由可逆σI变换严格证明共同非零尺度在实际Gaussian KL中消去；适用于退化特征族的通用不变性也成立。

实际导出定理：midpointFrozen_offdiagonal_uniform_bound、midpointFrozen_matrix_uniform_bounds、midpoint_whitened_gram_uniform_floor、scaledHarmonizableGaussian_midpoint_klDiv。全部声明清单和文件哈希见[记录](verification/lean_formalization_progress.json)。

## 边界与剩余部分

没有把目标谱下界当作假设：它由实际归一化谱特征、冻结行和与V扰动推出。小量条件明确保留；不要求B log n趋于零。

本阶段尚未证明混合项Q的O(B log n/n)逐项界，因此未宣称实际总Frobenius/KL速率已完成，也没有宣称minimax下界或最优性完成。具体packing与渐近量词、上界与极限定理继续保留在[主线状态](mainline_status.md)。

未改动20份既有书面证明、原PDF或backlog范围。审计结果见[审计记录](verification/audit_result.json)。
