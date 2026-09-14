# 22. 一维 q1 长记忆主线的修复证明与 Lean 交接

日期：2026-09-14。源码基准：`9ba36f6`。

本文是书面证明及形式化任务说明，**不是新增 Lean 定理已经通过的声明**。它修复最终长记忆定理的两个不可满足前提，并补写从实际矩阵到有符号二阶混沌、对数统计量和已知尺度估计器的论证。符号与现有仓库对齐；通用分析和概率步骤仍须由接手 agent 形式化，不能换名登记为已获准的外部文献假设。

**后续支撑已另行展开：** [文件23](23_spectral_probability_support.md)给出循环积分 L² 界、HS 专用工具、谱构造、正负谱分别匹配、Gaussian 级数全序列 a.e. 收敛及现成谱截断接口；[文件24](24_endpoint_and_validation_contracts.md)给出实际端点的归一化约束、最终同律、四阶余项、真值中心条件，以及未知尺度的一组保守可行带宽。接手实现时以这两份补充中选定的接口为准，不必同时重做本文件的矩生成函数路线。

## 0. 总体判断与本次范围

1. 主线尚不能验收完成。当前最终定理的全行非空前提、带宽前提各自导致矛盾，详见[独立审计](../verification/independent_mainline_audit_2026-09-14.md)及[Lean 反证](../verification/CapstonePremiseAudit.lean)。这否定的是该形式化端点的适用性，不是否定论文的长记忆极限。
2. 无须重做整个项目。实际协方差误差、权重逼近、Riesz 能量、循环积分求积和无维数损失的迹估计均有现成 Lean 定理。最短修复路线是实际矩阵直接比较 Riesz 矩阵。
3. 本文证明的统计结论是一维、q=1、固定内部点、已知常尺度（或预先除去该尺度）、**以真实期望为中心**的长记忆极限。允许有符号局部多项式权重。未知尺度、以真值为中心的偏差条件、联合 pilot、高维和完整 minimax 最优性不由本证明自动解决。
4. [原书面文件14](14_q1_long_memory_limit.md)已有谱构造及概率论证。本文保留其可复用部分，把实际矩阵比较替换成与当前 Lean 直接对应的路线，并细化带宽、非空性及四阶余项。本文与旧“FINAL”状态冲突时，以本文的明确边界为准。

## 1. 模型、归一化与要证明的结论

采用仓库的实际 harmonizable Gaussian 中点观测模型、固定光滑核及局部多项式设计。假设

\[
p\ge1,\quad M\ge0,\quad 0<a\le b<1,\quad
f\in\mathrm{hurstHolderClass}(p,M),\quad a\le f(x)\le b\ (0<x<1),
\]

并固定 \(t\in(0,1)\)、多项式次数 \(r\in\mathbb N\)。记

\[
h=f(t)>3/4,\qquad \psi=2-2h\in(0,1/2),\qquad c=h(2h-1)>0.
\]

选取多项式带宽，要求且只在本路线中要求

\[
\boxed{0<\gamma<1,\qquad (1-\gamma)\psi<2-2b.}                 \tag{B}
\]

对 \(n\ge1\)，令 \(\delta_n=n^{-\gamma}\)、\(S_n=n\delta_n\)。\(n=0\) 行按原程序定义或任意安全方式补齐；下文只使用最终性质。

设活动集大小为 \(m_n\)，按递增次序编号 \(i=0,\ldots,m_n-1\)。令

\[
w_{n,i}=\text{实际局部多项式权重},\quad
u_{n,i}=S_nw_{n,i},\quad z_{n,i}=2(i+1)/m_n-1,
\quad \omega=\mathrm{equivalentKernel}(r).
\]

活动的一阶增量经各自真实标准差归一化后为 \(Y_{n,i}\)，相关矩阵为 \(C_n=(\rho_{n,ij})\)。非退化性在第3节证明。

定义实际二阶项

\[
Q_n=S_n^\psi\sum_i w_{n,i}(Y_{n,i}^2-1)
    =S_n^{\psi-1}\sum_i u_{n,i}(Y_{n,i}^2-1).                 \tag{1}
\]

定义行加权矩阵（一般不对称）及 Riesz 比较矩阵

\[
A_n=S_n^{\psi-1}\operatorname{diag}(u_n)C_n,
\]
\[
T_n(i,j)=
\begin{cases}
cS_n^{\psi-1}\omega(z_{n,i})|i-j|^{-\psi},&i\ne j,\\
0,&i=j.
\end{cases}                                                   \tag{2}
\]

二者分别对应 `actualQ1NormalizedActualMatrix`、`actualQ1RieszMatrix`。不要把 \(A_n\) 当成 Hermitian 矩阵；实际自伴二次型矩阵另记为

\[
B_n=S_n^{\psi-1}C_n^{1/2}\operatorname{diag}(u_n)C_n^{1/2}.
                                                                    \tag{3}
\]

对 \(k\ge2\)，定义绝对收敛的循环积分

\[
J_k=c^k\int_{[-1,1]^k}\prod_{j=1}^k
 \omega(x_j)|x_j-x_{j+1}|^{-\psi}\,dx,
\qquad x_{k+1}=x_1.                                             \tag{4}
\]

对角超平面上的被积函数可定义为零；其零测集取值不改变积分。下文证明存在实数列 \(\lambda\in\ell^2\)，满足 \(\sum_j\lambda_j^k=J_k\)，且

\[
Q=\sum_{j\ge0}\lambda_j(Z_j^2-1),\quad Z_j\ \text{独立标准正态},
\qquad Q_n\Rightarrow Q.                                       \tag{5}
\]

进一步，若 \(\widehat G_n\) 是相应的实际加权对数平方增量统计量，\(\widehat H_n\) 是仓库 q1 校准函数在 \([0,1]\) 上的截断逆，则

\[
S_n^\psi(\widehat G_n-E\widehat G_n)\Rightarrow Q,
\qquad
2S_n^\psi\log n(\widehat H_n-E\widehat H_n)\Rightarrow -Q.       \tag{6}
\]

## 2. 引理 W1：带宽与截断可同时选择

由于 \(h\le b<1\)，

\[
L:=\frac{b-h}{1-h}\in[0,1),\qquad
(1-\gamma)(2-2h)<2-2b\iff \gamma>L.
\]

因此例如 \(\gamma=(1+L)/2\) 总满足 (B)。例：\(h=0.9,b=0.95,\gamma=0.75\)，左侧为 \(0.05<0.1\)。此例还说明不必要求旧条件 \(\gamma<4h-3=0.6\)。这是带宽区间的非空性证明，不代替其他模型前提的实例化。

\(\delta_n\to0\)、\(S_n=n^{1-\gamma}\to\infty\)。活动集几何给出

\[
m_n/S_n\to2,\quad m_n\to\infty,\quad
\text{最终 }0<m_n\le3S_n.                                      \tag{7}
\]

选

\[
\theta=\frac{1-2\psi}{2}>0,\qquad
R_n=\lfloor S_n^\theta\rfloor+1.
\]

则 \(R_n\ge1\)、\(R_n\to\infty\)，最终 \(2R_n+1\le5S_n^\theta\)，因而

\[
0\le S_n^{2\psi-2}m_n(2R_n+1)
 \le15S_n^{2\psi-1+\theta}\to0,                               \tag{8}
\]

因为指数 \(2\psi-1+\theta=-(1-2\psi)/2<0\)。**\(\theta\) 控制截断，\(\gamma\) 控制带宽；无需比较 \(\gamma\) 与 \(4h-3\)。**

令仓库的网格误差为

\[
e_n=C_{\rm cov}(1+\log(2n))(n^{-1}+n^{2b-2}).
\]

它趋于零，且由 (B)

\[
S_n^\psi e_n\to0,                                             \tag{9}
\]

因为两个幂指数 \((1-\gamma)\psi-1\)、\((1-\gamma)\psi+2b-2\) 都严格为负。任意固定次幂的对数不影响该结论。

对任意固定见证常数 \(C_{\rm cov},C_{\rm tail}\ge0,L_0>0\)，设
\(D_n=2L_0(1+M)\delta_n\)、\(E_n=D_n\log n\)。仓库尾包络恰为

\[
\eta_n=18C_{\rm tail}D_n(1+e^{E_n}E_n)
 +9e^{E_n}E_n+\tfrac32D_n+4(2S_n)^\psi e_n+\frac{16}{R_n+1}.
                                                                    \tag{10}
\]

\(D_n,E_n\to0\)，结合 (9) 及 \(R_n\to\infty\) 可得 \(\eta_n\to0\)。这证明了实际核定理所需的 `hcut` 和完整量词形式的 `henv`。

**Lean 对接：** 复用 `poly_cutoff_satisfiable` 和 `secondChaosTailFreePart_tendsto_zero_powBandwidth`。现有 `polyBandwidth_cutoff_and_envelope` 的证明只用 `hγcut` 推出 \(\gamma<1\)；新版本直接接收 `hγ1 : γ < 1` 即可。不要调用仍要求旧带宽组合的 capstone。

## 3. 引理 W2：最终非空与实际增量非退化

(7) 已给出最终非空。不得要求 `∀ n, 0 < m n`；原定义在 \(n=0\) 和 \(n=1\) 的活动集为空。

对实际归一化增量特征 \(v_{n,i}\)，已有协方差逼近给出

\[
\left|\|v_{n,i}\|^2-1\right|\le e_n
\]

一致于活动下标。这里冻结增量的归一化平方范数恰为1。由 \(e_n\to0\)，最终 \(\|v_{n,i}\|^2\ge1/2\)，从而所有活动特征非零。原始增量特征与之相差一个非零尺度，故同样非零。

**Lean 对接：** `hurstHolder_stride_first_covariance`、`normalizedFrozenIncrement_norm_sq`、`gridStrideFirst_feature_identity`；`first_stride_rows_of_covariance_lt_one` 中已有这一范数下界证明。接入 `actualQ1Coeff`/`actualQ1Obs` 的特征恒等式。此处应输出 `∀ᶠ n in atTop, ∀ i, ... ≠ 0`。

有限多个坏行可直接在渐近定理内排除，也可安全补行后用最终同律转回。优先让新的消费定理接受最终非退化及 \(m_n\to\infty\)，避免对 \(n=0\) 构造不存在的下标。

## 4. 引理 W3：实际矩阵的 Frobenius 收敛及一致有界性

本节范数一律为 Frobenius 范数 \(\|D\|_F^2=\sum_{ij}D_{ij}^2\)。

实际权重逼近给出

\[
\max_i|u_{n,i}-\omega(z_{n,i})|\to0                            \tag{11}
\]

记无权比较核为 \(V_{n,ij}=S_n^\psi\rho_{n,ij}\)、\(K^{\rm Riesz}_{n,ij}=c(S_n/|i-j|)^\psi\)（对角为零）。W1 实际尾估计给出远带的 \(|d^\psi\rho-c|\le\eta_n\)。因此无权误差能量可直接分带估计：近带中 \(|\rho|\le1\)，且非对角时 \(d^{-\psi}\le1\)，贡献至多

\[
2(1+c^2)S_n^{2\psi-2}m_n(2R_n+1)\to0.
\]

远带中 \(|\rho-cd^{-\psi}|\le\eta_n d^{-\psi}\)，所以误差能量至多

\[
\eta_n^2 S_n^{2\psi-2}\sum_{i\ne j}|i-j|^{-2\psi}\to0.
\]

最后一步用每个距离在每行最多出现两次，以及
\(\sum_{d=1}^{m}d^{-2\psi}\le C_\psi m^{1-2\psi}\)、\(m_n\le3S_n\)，可知乘在 \(\eta_n^2\) 后的量一致有界。

由 (11)，\(|u_{n,i}|\le U\) 最终一致成立。置 \(\varepsilon_n=\max_i|u_{n,i}-\omega(z_{n,i})|\)，将带权差写成
\(u_{n,i}(V_{n,ij}-K^{\rm Riesz}_{n,ij})+(u_{n,i}-\omega(z_{n,i}))K^{\rm Riesz}_{n,ij}\)。其能量至多无权误差能量的 \(2U^2\) 倍，加上 Riesz 能量的 \(2\varepsilon_n^2\) 倍。因此

\[
\|A_n-T_n\|_F^2
=S_n^{-2}\sum_{ij}
 \big[u_{n,i}S_n^\psi\rho_{n,ij}
       -\omega(z_{n,i})K^{\rm Riesz}_{n,ij}\big]^2\to0.         \tag{12}
\]

活动下标连续，故实际下标距离等于秩编号距离。这就是仓库的精确能量恒等式，不含额外 \(m_n\) 因子。

设 \(B_\omega\ge0\) 满足 \(|\omega|\le B_\omega\)。已有 Riesz 能量界在 \(S\ge1,m\le3S\) 下为

\[
S^{-2}\sum_{ij}(K^{\rm Riesz}_{ij})^2\le
C_{\rm ref}:=2c^2\left(3+\frac{3\,4^{1-2\psi}}{1-2\psi}\right).
\]

所以 \(\|T_n\|_F\le B_\omega\sqrt{C_{\rm ref}}\)，再用三角不等式与 (12)，存在固定 \(C\ge1\) 使最终

\[
\max(\|A_n\|_F,\|T_n\|_F)\le C.                             \tag{13}
\]

**Lean 对接：** `actualQ1_meshEnergy_tendsto_zero` → `actualQ1_frobenius_norm_tendsto_zero`；`rankRieszKernel_energy_le_const` → `actualQ1UniformFrobeniusBound_of_bounded`。这几步均有现成证明；新的工作是以 W1 的可行带宽数据拼接。

## 5. 引理 W4：无维数损失的迹幂转移

任意同阶实矩阵 \(A,T\)、整数 \(k\ge2\)，若 \(\|A\|_F,\|T\|_F\le C\)，则

\[
\boxed{|\operatorname{tr}(A^k)-\operatorname{tr}(T^k)|
 \le kC^{k-1}\|A-T\|_F.}                                    \tag{14}
\]

**证明。** 非交换望远镜恒等式为

\[
A^k-T^k=\sum_{s=0}^{k-1}A^s(A-T)T^{k-1-s}.
\]

对每项用迹的循环性，把 \(A-T\) 单独作为一个因子。因为其余因子总次数为 \(k-1\ge1\)，其乘积的 Frobenius 范数至多 \(C^{k-1}\)。这里零次幂应直接消去，不能使用错误的 \(\|I_m\|_F\le1\)。由
\(|\operatorname{tr}(XY)|\le\|X\|_F\|Y\|_F\) 及三角不等式即得 (14)。证毕。

结合 (12)–(13)，对每个固定 \(k\ge2\)，

\[
\operatorname{tr}(A_n^k)-\operatorname{tr}(T_n^k)\to0.          \tag{15}
\]

**Lean 对接：** 直接使用 `FarWordAssembly.abs_trace_pow_sub_le_frob`（实际命名空间为 `Hurst`）。它不要求矩阵对称，不要求权重非负。原 `mesh_frobenius_trace_pow_tendsto` 引入的维数损失在这里不必要；不再证明 `hPert` 或 `hFrozenPert`。

建议新增一个泛型定理 `trace_pow_sub_tendsto_zero_of_frobenius`：输入最终共同范数上界、差的范数趋零及 `2 ≤ k`，输出迹差趋零。证明只需 (14)、`filter_upwards`、`squeeze_zero'` 和常数乘极限。

## 6. 定理 W5：全部实际谱幂和收敛

由 \(m_n/S_n\to2\)、\(m_n\to\infty\)、\(0<\psi<1/2\) 及 \(\omega\) 连续有界，已有循环积分求积定理给出

\[
\operatorname{tr}(T_n^k)\to J_k\quad(k\ge2).                  \tag{16}
\]

结合 (15) 得 \(\operatorname{tr}(A_n^k)\to J_k\)。有限维迹循环恒等式又给

\[
\operatorname{tr}(B_n^k)=\operatorname{tr}(A_n^k)
 =\sum_{j<m_n}\lambda_{n,j}^k\longrightarrow J_k,              \tag{17}
\]

其中 \(\lambda_{n,j}\) 为自伴矩阵 \(B_n\) 的实特征值，允许正负号。

**Lean 对接：** `hasWeightedRieszCycleQuadrature_instance`、`weightedRieszDiscrete_trace_pow_tendsto`、`hermitian_trace_pow_eq_sum_eigenvalues_pow`、`trace_pow_weightedFeatureQuadraticMatrix_eq`、`actualQ1_diagonalCorrelation_eq`。

建议先证明结论直接为 \(J_k\) 的新定理，而非输入 `hRiesz` 后立即换成 \(\sum\lambda_j^k\)。这样实际模型分析已经完成到哪里清晰可查。此定理应无 `hcard`、`hγcut`、`hγdec`、`hPert`、`hFrozenPert`、`hwnn`、`hRiesz`、`hQ` 参数。

## 7. 引理 W6：构造有符号 Riesz 谱

本节细化文件14的谱构造，是通用实分析/算子论证明，尚不宣称其 Lean 已闭合。

在实 Hilbert 空间 \(E=L^2([-1,1])\) 上定义

\[
(Kf)(x)=c\int_{-1}^1|x-y|^{-\psi}f(y)\,dy.
\]

核平方积分为

\[
\|K\|_{\rm HS}^2
=c^2\frac{2\,2^{2-2\psi}}{(1-2\psi)(2-2\psi)}<\infty.
\]

故 \(K\) 是自伴紧算子。它还非负：对 \(s>0\)，

\[
e^{-s|x-y|}=2s\int_{-\infty}^{\min(x,y)}
e^{-s(x-u)}e^{-s(y-u)}\,du,
\quad
|x-y|^{-\psi}=\frac1{\Gamma(\psi)}
\int_0^\infty s^{\psi-1}e^{-s|x-y|}\,ds.
\]

对有界 \(f\) 积分，将 \(\langle f,Kf\rangle\) 写成非负平方的积分。绝对交换由 \(\psi<1\) 和有限区间保证。再以有界函数在 \(L^2\) 中的稠密性及 \(K\) 有界性推广到所有 \(f\in E\)。

令 \(W=M_\omega\)，定义自伴算子 \(B=K^{1/2}WK^{1/2}\)。不要求 \(\omega\ge0\)。取 \(K\) 的非零谱 \(\kappa_i\ge0\) 及相应正交特征向量；零空间由平方根自动消去。利用 \(2\kappa_i\kappa_j\le\kappa_i^2+\kappa_j^2\) 与 Bessel 不等式，

\[
\begin{aligned}
\|B\|_{\rm HS}^2
&=\sum_{ij}\kappa_i\kappa_j|\langle e_i,We_j\rangle|^2\\
&\le\tfrac12\sum_{ij}(\kappa_i^2+\kappa_j^2)
 |\langle e_i,We_j\rangle|^2
\le\|\omega\|_\infty^2\sum_i\kappa_i^2<\infty.
\end{aligned}                                                   \tag{18}
\]

所以 \(B\) 有实平方可和特征值 \(\lambda_j\)。这里并未假设 \(K\) 是迹类。

下面核对 \(\operatorname{tr}(B^k)=J_k\)：

* 取 \(K\) 的有限谱截断 \(K_N\)。令 \(P_N\) 为对应谱投影，则 \(B_N'=K_N^{1/2}WK_N^{1/2}=P_NBP_N\to B\) 于 HS 范数；同时 \(WK_N\to WK\) 于 HS 范数。
* 有限秩迹循环性给出 \(\operatorname{tr}((B_N')^k)=\operatorname{tr}((WK_N)^k)\)。这不要求 \(W\) 保持 \(P_N E\)：可把有限秩乘积在包含其像的有限维子空间中计算，或直接循环移过有限秩因子。
* 两个 HS 因子的乘积是迹类，且 \(\|UV\|_1\le\|U\|_{\rm HS}\|V\|_{\rm HS}\)。用与 W4 相同的望远镜估计，取极限得 \(\operatorname{tr}(B^k)=\operatorname{tr}((WK)^k)\)。
* 将非负核截成 \(K^{(L)}(x,y)=\min(c|x-y|^{-\psi},L)\)。其 HS 范数不超过 \(\|K\|_{\rm HS}\)，算子范数不超过 \(\|K\|_{\rm op}\)，后者由 \(|K^{(L)}f|\le K|f|\) 得出。**核逐点非负不等于算子半正定**；此处不需要截断算子半正定。
* 有界核的循环积分由 Fubini 等于幂迹。无权循环积分非负，且至多 \(\|K\|_{\rm HS}^2\|K\|_{\rm op}^{k-2}\)。令 \(L\uparrow\infty\)，单调收敛证明无权循环积分有限。乘 \(\|\omega\|_\infty^k\) 即控制带权积分的绝对值。
* 最后对带权积分用主导收敛，对算子幂迹用 HS 连续性，得到 \(\operatorname{tr}((WK)^k)=J_k\)。

综上

\[
\sum_j\lambda_j^2<\infty,\qquad
\sum_j\lambda_j^k=J_k\quad(k\ge2).                            \tag{19}
\]

这是 `IsWeightedRieszSpectrum` 的存在性及适用性证明。任意 \(k\ge2\) 的绝对可和性由 \(\ell^2\subset\ell^\infty\) 推出。不能以一个未经构造的 `hRiesz` 宣告本节完成。

## 8. 引理 W7：构造 Q，并由全部有符号幂和推出分布收敛

在标准正态的可数乘积概率空间上取独立坐标 \(Z_j\)。由

\[
E\left|\sum_{j=N}^{M}\lambda_j(Z_j^2-1)\right|^2
=2\sum_{j=N}^{M}\lambda_j^2\to0,
\]

部分和在 \(L^2\) 中收敛至 \(Q\)。它们也是 \(L^2\) 有界鞅，故鞅收敛定理给出几乎处处收敛，且该极限与 \(L^2\) 极限一致。这提供 `IsSecondChaosSeriesLaw` 要求的两种收敛和可测版本；只写 \(L^2\) 收敛尚不足以填其全部字段。

对最终非退化的实际行，有限 Gaussian 二次型的正交对角化给

\[
Q_n\overset d=\sum_{j<m_n}\lambda_{n,j}(Z_j^2-1).              \tag{20}
\]

由 (17) 的 \(k=2\)，存在固定 \(D\ge1\)，使最终

\[
\sum_j\lambda_{n,j}^2\le D^2,\quad
\max_j|\lambda_{n,j}|\le D,\quad \sum_j\lambda_j^2\le D^2.
\]

必要时增大 \(D\) 即可。有限多个初始行不影响弱收敛。

取 \(a>0\) 使 \(2aD<1\)。标准正态平方的直接积分及实对数展开给出，对 \(|s|\le a\)，

\[
\log E e^{sQ_n}
=\sum_{k=2}^\infty\frac{2^{k-1}s^k}{k}
 \sum_j\lambda_{n,j}^k.                                      \tag{21}
\]

该式绝对收敛，且其绝对值一致有界，因为
\(\sum_j|\lambda_{n,j}|^k\le D^{k-2}\sum_j\lambda_{n,j}^2\)。于是
\(\sup_n E e^{a|Q_n|}<\infty\)，利用 \(e^{a|x|}\le e^{ax}+e^{-ax}\)。对 \(Q\) 的有限部分同理，再用几乎处处收敛和 Fatou 得到 \(E e^{a|Q|}<\infty\)。

(21) 在零点附近一致解析，其累积量为

\[
\kappa_1(Q_n)=0,\qquad
\kappa_k(Q_n)=2^{k-1}(k-1)!\sum_j\lambda_{n,j}^k\quad(k\ge2).
\]

由 (17)、(19)，累积量逐阶趋于 \(Q\) 的累积量；普通矩是有限个累积量的多项式，故全部矩收敛。

为使“矩收敛 ⇒ 分布收敛”合法：二阶矩有界保证概率律紧；任意弱收敛子列的各阶矩由上述指数矩界保证一致可积，因而其极限继承 \(Q\) 的所有矩。极限也有一个正的指数矩（对截断指数函数用弱收敛，再单调收敛）。具有正指数矩的两个概率律若所有矩相同，则特征函数在包含实轴的复条带内解析、在零点附近 Taylor 展开相同，解析唯一性及特征函数唯一性推出两律相同。故所有子列极限都是 \(\mathcal L(Q)\)，得到 (5)。

**形式化选择：** 此证明使用全部 \(k\ge2\) 幂和，自动保留谱符号，无需 `hwnn` 或 `hNegMass`。接手 agent 也可用现成谱匹配和 \(L^2\) 耦合证明同一泛型结论，但必须覆盖一般有符号谱；仅有偶数幂和不能识别正负号。紧性、矩一致可积、解析唯一性及鞅收敛是明确的通用支撑步骤，需落实到 mathlib 定理或自行证明，不能把整段改称一个获准外部公理。

**实现路线补充：** 文件23 B1–D3 已把有符号谱匹配路线写完整，并核对现有 `centeredSpectralSquares_tendsto_secondChaos_of_padded_l2` 允许有符号系数。推荐先走这条路线；上面的矩/解析唯一性论证作为独立书面验证保留，不再要求接手 agent 把两条路线都形式化。

## 9. 引理 W8：全部高阶 Hermite 余项消失

本节给出可直接复用同一个 \(R_n\)、同一个尾包络的证明，避免额外要求 \(b<7/8\)。

令 \(g(y)=\log(y^2)-E\log Z^2\)，\(H_2(y)=y^2-1\)。已有 Hermite 展开说明 \(g-H_2\) 的最低阶为4。因此任意标准 Gaussian 对 \((Y,Y')\) 的相关系数为 \(\rho\) 时，

\[
|E[(g-H_2)(Y)(g-H_2)(Y')]|\le C_g|\rho|^4,
\quad |E[g(Y)g(Y')]|\le V_g|\rho|^2.                          \tag{22}
\]

W3 所用的**无权**实际核能量定理还给出

\[
E_{2,n}:=S_n^{2\psi-2}\sum_{ij}\rho_{n,ij}^2=O(1).             \tag{23}
\]

注意不能从有符号加权二次型的方差反推 (23)；应直接调用无权核的 HS 收敛和 Riesz 能量界。

由 (11) 最终 \(|u_{n,i}|\le U\)，于是标准化余项 \(D_n^{\rm rem}\) 满足

\[
E|D_n^{\rm rem}|^2\le C_g U^2 S_n^{2\psi-2}
 \sum_{ij}|\rho_{n,ij}|^4.                                   \tag{24}
\]

将双和分成 \(d=|i-j|\le R_n\) 与 \(d>R_n\)。近带由 \(|\rho|\le1\) 控制，贡献至多
\(C_gU^2S_n^{2\psi-2}m_n(2R_n+1)\to0\)。

远带实际尾估计的精确形式是

\[
|d^\psi\rho_{n,ij}-c|\le\eta_n.
\]

因此 \(|\rho_{n,ij}|\le(c+\eta_n)R_n^{-\psi}\)，且远带贡献至多

\[
C_gU^2(c+\eta_n)^2R_n^{-2\psi}E_{2,n}\longrightarrow0.         \tag{25}
\]

由 W1、(23) 完成 (24) 的趋零证明。结合 (5) 与 Slutsky，得到 (6) 的第一个结论。

同样用 (22) 的第二个界和 (23)，得到

\[
\operatorname{Var}(\widehat G_n)=O(S_n^{-2\psi}).              \tag{26}
\]

**Lean 对接：** 远带用 `hurstHolder_q1_active_scaled_actual_tail_error_le_envelope`；无权能量用 `hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed`；对数 Hermite 分解见 `FeatureQuadraticLimit.lean`。建议直接证明带权四阶双和趋零，避免全网格行和产生不必要的范围限制。

## 10. 定理 W9：已知尺度估计器及真实期望中心

令 \(L_n=\log n\)，\(c_\sigma\) 表示已知尺度下的校准常数（单位尺度时为 `gaussianLogSquareMean`）。置

\[
\mu_n=E\widehat G_n,\quad
\vartheta_n=(c_\sigma-\mu_n)/(2L_n),\quad
\widetilde H_n=(c_\sigma-\widehat G_n)/(2L_n),\quad
\widehat H_n=\Pi_{[0,1]}\widetilde H_n.
\]

已有权重再现常数、权重绝对和有界及实际均值展开给出 \(\vartheta_n\to h\)。也可直接证明：每个实际对数增量的均值为 \(c_\sigma-2f(t_i)\log n+o(1)\)，误差在活动窗内一致；\(f(t_i)\to h\) 一致，且 \(\sum_iw_{n,i}=1\)、\(\sum_i|w_{n,i}|=O(1)\)。除以 \(2\log n\) 即得所需一致性。这里使用最终非退化和 \(|\log\|v_{n,i}\|^2|=O(e_n)\)。

取固定 \(d>0\)，使最终 \(\vartheta_n\in[d,1-d]\)。令 \(X_n=\widetilde H_n-\vartheta_n\)，则 \(EX_n=0\)，并且

\[
|\Pi_{[0,1]}(\vartheta_n+X_n)-(\vartheta_n+X_n)|
 \le |X_n|\mathbf1_{\{|X_n|\ge d\}}\le X_n^2/d.
\]

由 (26)

\[
2S_n^\psi L_n E|\widehat H_n-\widetilde H_n|
\le\frac{S_n^\psi\operatorname{Var}(\widehat G_n)}{2dL_n}
\to0.                                                        \tag{27}
\]

同一个界也证明 \(2S_n^\psi L_n|E\widehat H_n-\vartheta_n|\to0\)。未截断量有精确等式

\[
2S_n^\psi L_n(\widetilde H_n-\vartheta_n)
=-S_n^\psi(\widehat G_n-\mu_n).
\]

结合 (27) 便得 (6) 的第二个结论。整个证明保留负号；\(Q\) 通常不对称，不能把 \(-Q\) 换成 \(Q\)。

这证明的是以 \(E\widehat H_n\) 为中心的结论。若改成 \(h\)，必须另外处理 \(2S_n^\psi\log n(E\widehat H_n-h)\)；它可能趋于非零常数甚至发散。未知尺度还需在相同归一化下证明尺度误差可忽略，本文不假设该事实已经完成。

## 11. 推论 W10：极限非退化、非 Gaussian 与公式修正

\(\int\omega=1\)，故 \(\omega\ne0\)。对 \(\beta=2\psi\in(0,1)\)，第7节的 Laplace 分解给出

\[
J_2=c^2\iint\omega(x)\omega(y)|x-y|^{-\beta}\,dxdy>0.
\]

严格性说明：对每个 \(s>0\)，相应平方积分若为零，则
\(F_s(u)=\int_u^\infty\omega(x)e^{-s(x-u)}dx\) 几乎处处为零。\(F_s\) 连续且绝对连续，故处处为零；\(F_s'=sF_s-\omega\) 几乎处处推出 \(\omega=0\)，矛盾。积分交换由有界紧支撑及 \(\beta<1\) 保证。

因此 \(\operatorname{Var}(Q)=2J_2>0\)，且第四累积量 \(48\sum_j\lambda_j^4>0\)，故极限非 Gaussian。全实轴特征函数为

\[
\varphi_Q(u)=\exp\sum_j\left[-iu\lambda_j-
\tfrac12\operatorname{Log}(1-2iu\lambda_j)\right],\quad u\in\mathbb R,
\]

其中使用实部为正的半平面上的主对数。平方可和性控制尾部为 \(O_u(\lambda_j^2)\)，有限前项没有对数分支歧义。只有在 \(2|u|\sup_j|\lambda_j|<1\) 时才能进一步展开为

\[
\log\varphi_Q(u)=\tfrac12\sum_{k=2}^\infty\frac{(2iu)^k}{k}J_k.
\]

原文的长记忆归一化和二阶混沌类型可以保留；具体常数应使用 \(c=h(2h-1)\)，估计器极限取反射 \(-Q\)，全实轴公式不能直接用仅局部收敛的幂级数替代。

## 12. 接手 agent 的实现与验收顺序

| 编号 | 交付目标 | 当前可复用部分 | 仍需完成的 Lean 工作 |
|---|---|---|---|
| W1 | 可行带宽、截断、尾包络 | `ActualSecondChaosComplete.lean` 的独立标量引理 | 将 `hγcut` 改为真正需要的 `hγ1`；证明参数区间非空 |
| W2 | 最终活动非空、最终特征非零 | 活动集几何、实际协方差、范数恒等式 | 与实际观测/系数接口拼接；移除全行假设 |
| W3 | 实际→Riesz Frobenius 收敛、共同上界 | `ActualQuadratureConfluence.lean` | 使用 W1 的新带宽条件实例化 |
| W4 | 固定幂迹差趋零 | `FarWordAssembly.lean` 的尖锐界 | 新建简短泛型渐近包装 |
| W5 | 实际全部谱幂和→循环积分 | 求积、Hermitian 谱幂和及循环迹 | 直接拼接，不经过冻结矩阵 |
| W6 | 存在有符号平方可和谱及循环迹识别 | 书面文件14、第7节 | 算子构造与实际核适用性；不能保留为内部假设 |
| W7 | 构造 Q；有符号幂和→二次型弱收敛 | 现有 Gaussian 二次型/谱工具 | 完成一个覆盖有符号谱的通用消费定理及 Q 的 a.e. 收敛字段 |
| W8 | 无限 Hermite 余项趋零 | 实际尾包络、无权能量、Hermite 余项界 | 第9节的近远带双和证明；不额外限制 b<7/8 |
| W9 | 已知尺度估计器期望中心极限 | 现有反演、均值、可测性工具 | 在同一带宽及同一统计量上接完，保留 −Q |
| W10 | 非退化及非 Gaussian、特征函数 | 旧书面证明及部分分布工具 | 逐项核对当前 Lean 覆盖，不以公式定义代替证明 |

建议先建立新模块，例如 `ActualSecondChaosDirectTrace.lean`，保留旧文件以便比较。新模块路径和上文建议的新定理名尚未创建。

一次只验证一层。先让 W1–W5 通过编译并检查最终声明；随后构造 W6–W7；再消费到 W8–W9。若先完成非负权重特例，必须将标题和状态限定为该特例，一般权重仍标待完成。

最终验收必须同时满足：

1. 新最终定理的假设可满足；显式给出常数 H 的合法模型及带宽实例，并覆盖 \(b\) 与 \(h\) 不接近时的参数区间检查。
2. 声明中没有未证明的内部 `hRiesz`、`hQ`、`hcard`、`hane`、`hwnn`、`hPert` 等输入。内部产生的局部变量当然可以使用这些名字；关键是它们不能作为未消除的最终参数。
3. 主结论确实使用实际观测、实际权重、正确归一化及真实期望中心；不可用抽象 Gaussian 数组替换最终模型实例。
4. 仅有 `lake build` 和 `#print axioms` 通过不够；还要检查模型参数范围、量词和非空性。状态登记不得先于实际定理完成。
5. 更新摘要时分别记录已知尺度、未知尺度、期望中心、真值中心、有符号权重和非负特例；不自动扩大到原27个编号的完整完成。

可复现命令（从项目根目录运行）：

```sh
/Users/jinqishen/.elan/bin/lake build Hurst
/Users/jinqishen/.elan/bin/lake env lean verification/CapstonePremiseAudit.lean
/Users/jinqishen/.elan/bin/lake env lean verification/AxiomAudit.lean
git diff --check
```

本次重新运行了原 capstone 两项矛盾的独立 Lean 证明，退出码为0。本文件是新书面证明；W1–W10 的新组合、扩展接口和泛型支撑尚未作为一套新 Lean 定理编译。本次没有修改任何 `Hurst/*.lean` 主线文件。
