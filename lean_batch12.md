# 第十二阶段：Gaussian偶函数协方差与实际加权方差

新增51条数学定理，累计565条数学定理及3条编号检查。完整原编号结果仍为2/27。主线未完成。

直接证明见[证明说明](proof_notes/gaussian_even_covariance.md)。从实际Gaussian密度出发，计算密度重叠；正交旋转后把相关rho和−rho的密度平均。平均密度相对独立基准的平方误差是rho⁴/(1−rho⁴)。Cauchy–Schwarz与大相关系数情形的普通L²界合起来，得到全部联合标准Gaussian偶函数协方差界，包括退化相关rho=±1。

对任意非零方差的中心联合Gaussian，最终证明

|Cov(log X², log Y²)| ≤ 4 V_log Corr(X,Y)²，

其中V_log是标准Gaussian的log平方方差。标准化、几乎处处非零、可积性、加常数不改变协方差均已在Lean处理。此证明无需Hermite完备性。

真实Hilbert特征Gaussian模型中的加权统计量满足

Var(Σ w_i log D_i²) ≤ 4 V_log Σ_i Σ_j |w_i| |w_j| rho_ij²。

若max|w_i|≤W、Σ|w_i|≤L、每行Σrho_ij²≤R，则进一步≤4 V_log L W R。这里最后的行和条件是显式输入；本阶段没有把它冒充为实际mBm已证性质。

尚需变化Hurst的q=1/2相关衰减与求和、q=2抵消、统一高阶矩、估计器风险、未知尺度和三个记忆极限。
