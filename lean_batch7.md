# 第七阶段：实际KL主界与Proposition 8.1

新增39条数学定理：MixedPower 10、CovarianceParameter 2、MixedKernel 9、MidpointFrobenius 8、MidpointKL 10。累计352条数学定理和3条编号检查。Proposition 8.1已完整形式化，原编号完整结果为1/27；主线未完成。

## 从实际模型到最终结论

网格幂函数与x^p log x的空间差分单独覆盖零端点。协方差归一化系数及参数导数在紧参数矩形上有统一界。先消去核中的纯时间背景项，再作参数中值估计，得到真实混合项绝对值≤K B(1+log(2n))/n。该步骤未增加独立性或未证明的混合界前提。

实际V列能量≤(D B)²。结合冻结Frobenius界以及Q与转置项，得到完整白化Gram误差平方和≤C(na²+B²)(1+log(2n))²（B≤1）。这一步包含所有协方差项。

随后合并上一阶段的完整Gram正谱下界与Gaussian KL公式，导出统一正常数c₀、b₀、C：对n≥1、a log(2n)≤c₀、B≤b₀，实际共同非零尺度模型满足KL≤C(na²+B²)log²(2n)。不要求B log n趋于零，因此覆盖文件20的p=1核心KL修复。

## 原Proposition 8.1

最终定理为`Hurst.proposition_8_1_function_limsup`。它接收真实Hurst函数序列H_n、对应真实导数、(0,1)到(0,1)的值域条件、原一致幅度/导数界及(a_n+B_n)log n→0。通过中值定理推出观测点离散Lipschitz条件，再证明小量阈值最终满足，换回log n，最终得到原式(8.4)的归一化KL limsup上界。

KL是实际有限维Gaussian测度的散度。有限样本不等式先证明其最终有限，再用于实数limsup；没有利用无穷值转实数的约定掩盖散度发散。共同σ可以随n变化且非零，涵盖原固定正σ范围。网格始终是原中点网格。

本原命题的结论无需更改阶数。证明中的谱归一化、半步长和接触区间等问题已用新证明处理。

## 尚未完成

Theorem 3.1仍需具体bump packing、原固定Hölder半范数类归属、Ls分离和最终minimax渐近量词。MSE、高阶风险、未知尺度估计链和相关Gaussian极限定理仍有待完成。不能把本命题完成表述为整个minimax或主线完成。

[主线状态](mainline_status.md)；[逐声明及哈希](verification/lean_formalization_progress.json)；[公理审计](verification/audit_result.json)。20份既有书面证明、原PDF和backlog范围保持不变。
