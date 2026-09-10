# 实际相关对数统计量的一致 Hermite 截断

对应书面文件11第4节、13第3节；同时提供文件19所需的二阶相关控制。以下均已在本项目Lean中证明，尚不包含有限多项式CLT或高阶矩界。

令γ=N(0,1)，g(x)=log(x²)−Elog(Z²)，e_m=H_m/√(m!)为已证明完备的Hermite基。定义

\[
 a_m=\langle e_m,g\rangle,\quad P_K=\sum_{m<K}a_me_m,\quad R_K=g-P_K.
\]

与书面证明的“m≤K”仅有索引平移。`HermiteTruncation`证明R_K→0于L²(γ)，保留前两阶系数为零；`HermiteTailEnergy`证明

\[
\|R_K\|_2^2=\operatorname{Var}(\log Z^2)-\sum_{m<K}a_m^2\longrightarrow0.
\]

`HermitePolynomialTruncation`证明实际有限多项式P_K与Hilbert空间元素几乎处处相等。

设X_i是任意有限个标准Gaussian观测，两两联合Gaussian，ρ_ij=Cov(X_i,X_j)。由已证明的真实联合Hermite展开，

\[
|E[R_K(X_i)R_K(X_j)]|\le\rho_{ij}^2\|R_K\|_2^2.
\]

若max_i∑_jρ_ij²≤B，则对于任意有符号实权重w，

\[
E\left|\sum_iw_iR_K(X_i)\right|^2
\le B\|R_K\|_2^2\sum_iw_i^2.
\]

证明使用2|w_iw_j|≤w_i²+w_j²与相关矩阵对称性。`WeightedSchur`、`HilbertSchur`和`GaussianArrayL2`证明这一步，包含函数可积性以及实际二阶矩与L²范数的身份。

对于原模型线性观测D_i，`FeatureStandardGaussian`证明X_i=D_i/√Var(D_i)的实际标准Gaussian law。`FeatureHermiteApproximation`证明

\[
\log D_i^2-E\log D_i^2=g(X_i)\quad\text{a.s.}
\]

正方差和D_i≠0几乎处处均来自实际谱特征，没有略过对数在零点的奇性。因而G=∑w_i log D_i²、G_K=∑w_iP_K(X_i)满足同一误差界。

`WeightEnergy`从已证明的实际局部多项式权重稳定性推出(nδ)∑w_i²≤D，包括t=0、1。`GridHermiteApproximation`代入已证明的实际相关行和和非退化性，得到

\[
(n\delta)E|G-EG-G_K|^2\le C\|R_K\|_2^2.
\]

范围为：q=2,p≥2,0<a≤H≤b<1；或固定正整数步长的一阶差分,p≥1,0<a≤H≤b<3/4。固定Hölder类、固定多项式阶数后，C、样本阈值与局部样本阈值不依赖H、t、δ、K。因此给定ε>0可选统一K₀，使所有K≥K₀、充分大的n、整个允许的Hurst类与局部设计均满足归一化误差小于ε。

最后，`L2TestApproximation`与`FeatureHermiteTests`证明：若φ有界且1-Lipschitz，则

\[
|E\phi(c(G-EG))-E\phi(cG_K)|
\le\sqrt{c^2E|G-EG-G_K|^2}.
\]

取c=√(nδ)即得分布极限传递所需的一致测试函数误差。要完成CLT，仍需证明固定K的相关多项式阵列CLT及实际极限方差；本阶段没有把它们假设为已完成。临界情形的不同归一化与长记忆二阶混沌极限亦未由本结论解决。
