# Gaussian Hermite 基础及其与主线的关系

本文记录从 mathlib 基础独立实现的证明，未将 Hermite 完备性、联合矩公式或阵列极限定理设为前提。

1. 对多项式与标准 Gaussian 权重做全实轴分部积分。验证可积性和两个无穷端点的消失后，推出 Stein 恒等式。
2. 从 Hermite 递推证明导数递推，再由 Stein 恒等式证明全部正交关系：E[H_n(Z)H_m(Z)] = 1_{n=m} n!。
3. 对有限测度证明：若每个实参数的指数矩存在，则全部单项式矩决定测度。证明使用复矩母函数的解析性和唯一性。
4. 若 f 属于 Gaussian L² 且与所有单项式正交，用 f 的正、负部分构造两个有限测度。Cauchy–Schwarz 使两个测度具有全部指数矩；矩相同蕴含测度相同，继而 f=0 几乎处处。这给出多项式的完备性。
5. Hermite 递推说明其线性包络对乘 X 封闭，因此包含所有多项式。正交性、完备性一起给出归一化 Hermite Hilbert 基、真实 L² 级数收敛和 Parseval 等式。
6. 对 rho²+s²=1，在 Gaussian 积分中再次使用 Stein 恒等式，得到 E[H_n(rho*x+s*Z)] = rho^n H_n(x)。Fubini 和已验证的多项式可积性给出相关对的联合 Hermite 公式。
7. 三角表示的分布通过真实 Gaussian 均值、方差与协方差识别，公式因而适用于任意联合标准 Gaussian 对，包含退化相关 rho=±1。用连续线性拉回和完整 Hilbert 展开得到任意 Gaussian L² 函数的相关级数。
8. 中心化 log-square 的零阶及所有奇数阶系数消失。在零点外对 x*log(x²)*exp(-x²/2) 求导，验证零点连续、无穷端点消失及导数可积后做半直线积分，得到 E[g(Z)H_2(Z)]=2。归一化系数为 sqrt(2)，所以 Hermite 阶数恰为 2。
9. 去掉 H_2 后的余项前四个系数为零，平方范数为 Var(log Z²)-2。相关级数和 Parseval 将 Hermite 阶数转成相应的相关幂次界。

这些是高阶矩和短/临界/长记忆极限所需的真实概率论基础，但还没有证明多指标图展开的求和界、所需三角阵列 CLT、长记忆算子收敛或全部 s>2 风险。不能以本阶段完成替代这些主线结果。当前精确审计状态见 verification/audit_result.json 和 mainline_status.md。
