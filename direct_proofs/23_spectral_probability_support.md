# 23. 后续支撑证明：循环积分、有符号谱匹配与 Gaussian 级数

日期：2026-09-14。接续[文件22](22_long_memory_repair_lean_handoff.md)的 W6–W7。

**用途与状态。** 本文把此前压缩叙述的内部引理逐一展开，并选定一条能消费已有 Lean 模块的路线。它是新书面证明，尚未整体形式化。文中“现有”只指已核对源码中存在的声明；新接口名均为建议名，不能据此登记 Lean 完成。

推荐顺序：A1–A6 构造 Riesz 谱；B1–B5 构造其有符号排序及实际系数极限；C1–C4 构造 Gaussian 级数律；D1–D3 接回实际统计量；E1–E3 验证非 Gaussian 性与特征函数。文件22的矩生成函数证明保留为数学上的另一条验证路线，**实现时优先使用本文件的谱截断路线**，不必同时开发两套概率极限定理。

## A. 循环积分与真正的谱：只补主线需要的算子工具

### A1. 二元 L² 核的复合估计

设各空间均为 σ 有限测度空间，实可测核 \(F(x,y)\)、\(G(y,z)\) 平方可积。定义

\[
H(x,z)=\int F(x,y)G(y,z)\,dy
\]

于积分存在的点，其余点取零。Cauchy–Schwarz 给出

\[
|H(x,z)|^2\le
\left(\int |F(x,y)|^2dy\right)
\left(\int |G(y,z)|^2dy\right).
\]

由 Tonelli 积分，\(H\in L^2\)，且

\[
\|H\|_2\le\|F\|_2\|G\|_2.                              \tag{A1}
\]

这里先用平方可积性保证几乎处处的截面积分存在，再用上述绝对界交换积分；不要先对未经证明可积的有符号乘积直接 Fubini。

### A2. 任意长度循环乘积的绝对可积性与连续性

对 \(k\ge2\)，核 \(F_j\in L^2(X_j\times X_{j+1})\)，其中 \(X_{k+1}=X_1\)，有

\[
\int\prod_{j=1}^k|F_j(x_j,x_{j+1})|\,dx_1\cdots dx_k
\le\prod_{j=1}^k\|F_j\|_2.                               \tag{A2}
\]

**证明。** \(k=2\) 时直接 Cauchy–Schwarz。\(k>2\) 时先对前 \(k-1\) 个绝对值核依次使用 A1，得到从 \(X_1\) 到 \(X_k\) 的复合核，L² 范数至多前 \(k-1\) 个范数的乘积；最后与反向核 \(|F_k(x_k,x_1)|\) 做 Cauchy–Schwarz。非负函数的积分换序用 Tonelli，因此不循环依赖绝对可积性。

定义 \(\Phi_k(F)=\int\prod_jF(x_j,x_{j+1})\)。若 \(\|F\|_2,\|G\|_2\le C\)，把乘积差逐项展开并对每项用 (A2)，得到

\[
|\Phi_k(F)-\Phi_k(G)|\le kC^{k-1}\|F-G\|_2.                \tag{A3}
\]

这适用于有符号、非对称核。于是 \(F(x,y)=\omega(x)c|x-y|^{-\psi}\) 在 \([-1,1]^2\) 上的循环积分直接绝对可积，因为 \(0<\psi<1/2\)、\(\omega\) 有界。**不必为了这一项另外实现整个迹类算子库或复杂的奇异循环积分分区。** A2 是文件22 W6 中截断核论证的可替换补充。

### A3. 本项目需要的 Hilbert–Schmidt 工具及证明

在可分实 Hilbert 空间 \(E\) 上固定可数正交规范基 \((e_i)\)。对有界算子 \(T\)，先定义

\[
\|T\|_{\rm HS}^2=\sum_i\|Te_i\|^2.
\]

以下仅在右侧有限时使用 HS 范数：

1. **基无关性与伴随。** 对另一正交规范基 \((f_j)\)，Parseval 和非负双和交换给
   \(\sum_i\|Te_i\|^2=\sum_{ij}|\langle f_j,Te_i\rangle|^2=\sum_j\|T^*f_j\|^2\)。再交换两个基，得到基无关性及 \(\|T^*\|_{\rm HS}=\|T\|_{\rm HS}\)。
2. **算子范数界。** 对有限线性组合 \(x=\sum_i x_ie_i\)，三角不等式及 Cauchy–Schwarz 给 \(\|Tx\|\le\|T\|_{\rm HS}\|x\|\)；由稠密性推广，故 \(\|T\|_{\rm op}\le\|T\|_{\rm HS}\)。
3. **乘以有界算子。** 逐项估计 \(\|UTe_i\|\le\|U\|_{\rm op}\|Te_i\|\)，得 \(\|UT\|_{\rm HS}\le\|U\|_{\rm op}\|T\|_{\rm HS}\)。对伴随应用同一结论得右乘版本。
4. **有限压缩。** 令 \(P_N\) 投影到前 N 个基向量。\(\|T-TP_N\|_{\rm HS}^2=\sum_{i\ge N}\|Te_i\|^2\to0\)；由伴随得到 \(P_NT\to T\)。所以 \(P_NTP_N\to T\) 于 HS 范数，进而于算子范数。有限秩算子逼近证明 \(T\) 紧。
5. **L² 核与 HS 一致。** 对平方可积核 \(F\)，Cauchy–Schwarz 先证明积分算子 \(T_F\) 有界。然后对几乎处处的 \(F(x,\cdot)\) 用 Parseval，再 Tonelli，得到 \(\sum_i\|T_Fe_i\|^2=\iint|F|^2\)。因此核 L² 收敛正好给相应算子的 HS 收敛。
6. **两个 HS 因子的迹配对。** 定义
   \(\tau(U,V)=\sum_i\langle U^*e_i,Ve_i\rangle\)。该级数绝对收敛且 \(|\tau(U,V)|\le\|U\|_{\rm HS}\|V\|_{\rm HS}\)。由 HS 内积的基无关性，\(\tau\) 基无关；将它写成绝对收敛的 \(\sum_{ij}u_{ij}v_{ji}\)，可得 \(\tau(U,V)=\tau(V,U)\)。

对 \(k\ge2\)，可把 \(\operatorname{tr}(T^k)\) 具体定义为 \(\tau(T,T^{k-1})\)。乘积至少保留两个 HS 因子。由有限压缩、有限维迹恒等式和上述界，可推出所需的线性性、乘积循环性，以及

\[
|\operatorname{tr}(T^k)-\operatorname{tr}(U^k)|
\le kC^{k-1}\|T-U\|_{\rm HS},                              \tag{A4}
\]

其中 \(\|T\|_{\rm HS},\|U\|_{\rm HS}\le C\)、\(k\ge2\)。这也是文件22 W4 的无限维版本。通过这一专用定义，可以避免先建立任意迹类算子的全部 API；定义仍必须证明基无关性，不能只选一个方便的基计算后擅自换基。

**算子乘積迹的有限压缩验证。** 对至少两个 HS 因子的有限乘积，将每个 HS 因子用有限压缩逼近，其他有界因子保持不动。逐项相减时用第3、6项控制差。近似乘积包含有限秩因子，循环恒等式归约到有限维；取极限便得到原乘积的循环恒等式。这里不把 \(\|P_N\|_{\rm HS}\) 当作有界量。

### A4. Riesz 算子的正性、紧性与可数谱

取 \(E=L^2([-1,1])\)，\(0<\psi<1/2,c>0\)。核
\(K(x,y)=c|x-y|^{-\psi}\) 的平方积分有限，故由 A3 得到紧自伴算子。

对 \(f\in E\)，绝对积分有界：

\[
\iint |f(x)f(y)K(x,y)|\,dxdy
\le\|f\otimes f\|_2\|K\|_2=\|f\|_2^2\|K\|_2.
\]

因此文件22 W6 的 Laplace 分解可直接推广到 L² 函数：

\[
\langle f,Kf\rangle
=\frac{2c}{\Gamma(\psi)}\int_0^\infty s^\psi
\int_{\mathbb R}\left(\int_u^\infty
 \widetilde f(x)e^{-s(x-u)}dx\right)^2du\,ds\ge0,             \tag{A5}
\]

\(\widetilde f\) 为区间外补零的函数。先对绝对值用 Tonelli 及上面的界保证积分交换，然后再对有符号函数使用 Fubini。不存在 \(x=y\) 处的点值障碍：等式只需要几乎处处成立。

Laplace 公式本身由 Gamma 积分定义中代换 \(v=s|x-y|\) 得到；指数核的平方分解则直接积分 \(2s\int_{-\infty}^{\min(x,y)}e^{-s(x+y-2u)}du=e^{-s|x-y|}\)。需同时记录 \(\Gamma(\psi)>0\)，以保证 (A5) 的非负系数。

紧自伴谱定理提供完备的正交特征分解。当前 mathlib 已有
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
和非零特征空间有限维的
`ContinuousLinearMap.finite_dimensional_eigenspace`。

将非零特征空间各取一个正交规范基，并加入零空间的正交规范基。由于 \(E\) 可分，所得正交族可数；其闭线性包由上述谱定理为整个 \(E\)。可数性可直接用可分空间的稠密可数点集证明：正交单位向量彼此距离 \(\sqrt2\)，在互不相交的小球中各选择一个稠密点，得到到可数集的单射。

于是可选正交规范特征基，满足 \(Ke_i=\kappa_i e_i\)、\(\kappa_i\ge0\)，且由 A3

\[
\sum_i\kappa_i^2=\|K\|_{\rm HS}^2<\infty.                   \tag{A6}
\]

先使用一个 `Countable` 索引类型也可以，最后再重编号；有限族可在**系数数列**中补零。不能为了补成 \(\mathbb N\) 索引而把零向量加入正交规范基，也不能假设有无穷多个非零特征值。

**无需单独调用平方根算子定理。** 在此特征分解上定义
\(K^{1/2}x=\sum_i\sqrt{\kappa_i}\langle e_i,x\rangle e_i\)。
由 \(\sup_i\kappa_i\le\|K\|_{\rm op}\) 和 Parseval，级数收敛并定义有界自伴算子；逐个基向量验证其平方为 \(K\)，再由稠密性推广即可。

### A5. 有符号权重下构造 B，并证明循环积分识别

令 \(W=M_\omega\)、\(B=K^{1/2}WK^{1/2}\)。\(W\) 自伴有界，\(B\) 自伴。其矩阵元为

\[
b_{ij}=\sqrt{\kappa_i\kappa_j}\,\langle e_i,We_j\rangle.
\]

用 \(2\kappa_i\kappa_j\le\kappa_i^2+\kappa_j^2\)、\(W=W^*\) 和 Bessel 不等式，得

\[
\sum_{ij}|b_{ij}|^2\le\|W\|_{\rm op}^2\sum_i\kappa_i^2.     \tag{A7}
\]

故 \(B\) 为 HS 紧自伴算子。设 \(K_N\) 为选定基的有限谱截断，\(B_N'=P_NBP_N\)。在该有限基上直接计算

\[
\operatorname{tr}((B_N')^k)
=\sum_{i_1,\ldots,i_k<N}
 \prod_{j=1}^k\kappa_{i_j}\langle e_{i_j},We_{i_{j+1}}\rangle,
\quad i_{k+1}=i_1.                                         \tag{A8}
\]

另一方面，有限秩核 \(K_N(x,y)=\sum_{i<N}\kappa_i e_i(x)e_i(y)\) 的循环积分展开，经有限和与积分交换，恰为 (A8)。每个一维积分形如 \(\int\omega e_i e_j\)，由 Cauchy–Schwarz 有限；不需要各 \(e_i\) 有界。

由 A3，\(B_N'\to B\) 于 HS 范数。由核与 HS 范数一致性，\(K_N\to K\) 于核 L² 范数，从而 \(\omega(x)K_N(x,y)\to\omega(x)K(x,y)\) 于 L²。分别对 (A8) 两侧使用 A4 和 A2，得到

\[
\operatorname{tr}(B^k)=
\int_{[-1,1]^k}\prod_j\omega(x_j)K(x_j,x_{j+1})\,dx=J_k.
                                                               \tag{A9}
\]

这条证明不需要宣称非对称的 \(WK\) 为正算子，也不需要假设 \(K\) 迹类。

### A6. 将 B 的谱整理成 `IsWeightedRieszSpectrum`

对 \(B\) 应用 A4 所用的紧自伴谱分解；这里特征值允许有正有负。将其非零实特征值按重数枚举为 \(\mu_j\)，有限时补零。A3 的基无关性给

\[
\sum_j\mu_j^2=\|B\|_{\rm HS}^2,
\qquad \sum_j\mu_j^k=\operatorname{tr}(B^k)=J_k\quad(k\ge2).
                                                               \tag{A10}
\]

高次幂绝对可和由
\(\sum_j|\mu_j|^k\le\|\mu\|_\infty^{k-2}\sum_j\mu_j^2\) 得到。重新排列非零项及插入零不改变这些绝对收敛的和；下一节将其整理为便于有符号匹配的 \(\lambda\)。

目标 Lean 输出必须包含 `Summable (fun j => λ j ^ 2)` 和每个 \(k\ge2\) 的 `HasSum`。只有 `tsum = Jk` 不够：Lean 的不可求和 `tsum` 有默认值，不能拿默认值当存在性证明。

## B. 全部幂和到有符号系数：详细的确定性证明

本节是独立于 Riesz 模型的泛型定理。输入有限实数组 \(a_{n,i}\)、\(m_n\to\infty\)，以及一个实平方可和谱 \(\mu\)，满足

\[
\forall k\ge2,\quad
\sum_{i<m_n}a_{n,i}^k\longrightarrow\sum_j\mu_j^k.            \tag{B0}
\]

不要求数组、极限谱非负，不要求行与行在同一空间。

### B1. 平方加权谱测度及连续测试函数收敛

由 (B0) 的 \(k=2\)，选 \(D\ge1\) 使最终
\(\sum_i a_{n,i}^2\le D^2\)、\(\sum_j\mu_j^2\le D^2\)。于是所有相关系数值位于 \([-D,D]\)。定义有限正测度

\[
\nu_n=\sum_{i<m_n}a_{n,i}^2\delta_{a_{n,i}},\qquad
\nu=\sum_j\mu_j^2\delta_{\mu_j}.
\]

对整数 \(q\ge0\)，

\[
\int x^q\,d\nu_n=\sum_i a_{n,i}^{q+2}
\to\sum_j\mu_j^{q+2}=\int x^q\,d\nu.
\]

故对每个多项式积分收敛。对任意连续 \(f:[-D,D]\to\mathbb R\)，用 Weierstrass 一致逼近选多项式 \(P\) 满足 \(\|f-P\|_\infty<\varepsilon\)。则

\[
\left|\int f\,d\nu_n-\int f\,d\nu\right|
\le 2D^2\varepsilon+
\left|\int P\,d\nu_n-\int P\,d\nu\right|\to_{limsup}2D^2\varepsilon.
\]

再令 \(\varepsilon\downarrow0\)，得到所有连续测试函数的积分收敛。无需把有限测度强行归一化为概率测度；总质量为零的情形也自动包含。

### B2. 从加权测度恢复阈值以上的特征值个数

固定 \(t>0\)，且 \(t\) 不是 \(\mu\) 的正特征值。函数
\(g_t(x)=x^{-2}\mathbf1_{(t,D]}(x)\) 在远离 \(t\) 处连续且有界，因此

\[
N_n^+(t):=\#\{i:a_{n,i}>t\}
=\int g_t\,d\nu_n\to\int g_t\,d\nu
=\#\{j:\mu_j>t\}=:N^+(t).                                  \tag{B1}
\]

**不连续测试函数步骤的补证。** 取 \(0<\varepsilon<t/2\)，以在 \([t-\varepsilon,t+\varepsilon]\) 上线性过渡的连续函数逼近 \(g_t\)，其误差由固定常数乘该小区间的测度控制。用一个连续的帽形函数控制 \(\nu_n\) 在该小区间的质量；先取 n 极限，再令 \(\varepsilon\downarrow0\)，误差趋于 \(\nu(\{t\})=0\)。这由 B1 的连续测试函数结论推出，不必额外假设 Portmanteau。

两边个数都为整数且右边有限（至多 \(D^2/t^2\)），所以 (B1) 实际推出最终精确相等。对 \(-a_{n,i}\)、\(-\mu_j\) 同理得到负特征值绝对值的阈值计数稳定。

### B3. 正谱与负谱分别排序，再交错补零

将正特征值按递减顺序记为 \(p_j\ge0\)，负特征值的绝对值按递减顺序记为 \(q_j\ge0\)，缺项补零。该排序存在：平方可和性使每个正阈值以上只有有限项；只要还有正项，其上确界为正且能在有限个大于该上确界一半的候选中取到最大值。递归取最大值并保留重数，每个非零项最终都会被选到。

对有限行，将 \(\max(a_{n,i},0)\) 排成 \(p_{n,j}\)，将 \(\max(-a_{n,i},0)\) 排成 \(q_{n,j}\)，二者均长度 \(m_n\)，其余补零。

对每个固定 j，B2 推出 \(p_{n,j}\to p_j\)、\(q_{n,j}\to q_j\)：

* 若 \(p_j>0\)，选任意接近 \(p_j\) 的 \(a<p_j<b\)，避开可数个谱点且 \(a>0\)。大于 a 的目标正谱至少有 j+1 项，大于 b 的至多 j 项。B2 的最终计数相等给 \(a<p_{n,j}\le b\)。令 a、b 向 \(p_j\) 靠近。
* 若 \(p_j=0\)，对任意非谱点 \(t\in(0,\varepsilon)\)，目标大于 t 的正谱至多 j 项，故最终 \(p_{n,j}\le t<\varepsilon\)。负谱同理。

定义

\[
\lambda_{2j}=p_j,\quad \lambda_{2j+1}=-q_j,
\qquad
v_{n,2j}=p_{n,j},\quad v_{n,2j+1}=-q_{n,j}\quad(j<m_n).
                                                               \tag{B2}
\]

则 \(v_n\) 长度为 \(2m_n\)，补零后逐坐标趋于 \(\lambda\)。它包含原行每个非零特征值恰一次，以及额外零值；因此
\(\sum_{j<2m_n}v_{n,j}^k=\sum_{i<m_n}a_{n,i}^k\) 对所有 \(k\ge1\) 成立。

**为何不直接把原行按数值递减排列？** 若正谱有无穷多项，则固定编号永远看不到负谱；仅按绝对值排序又会在 \(+a,-a\) 的并列处丢失符号稳定性。上述分别排序再交错的规则处理两种情况。

### B4. 平方和尾界及可交付的误差函数

置

\[
t_K=\sum_{j\ge K}\lambda_j^2\to0,
\qquad e_K=4t_K+\frac{2}{K+1}\to0.
\]

对每个固定 K，由总平方和收敛和有限前缀逐坐标收敛，

\[
\sum_{j=K}^{2m_n-1}v_{n,j}^2
\to\sum_j\lambda_j^2-\sum_{j<K}\lambda_j^2=t_K.
\]

因此最终尾和至多 \(t_K+1/(K+1)\)，特别满足

\[
\forall K,\quad\forall^{\rm eventually}n,\quad
2\sum_{j=K}^{2m_n-1}v_{n,j}^2\le e_K.                         \tag{B3}
\]

量词是“每个 K 有自己的足够大 n”，不需要对所有 K 共用一个 n 阈值。这与现有
`spectralTailBound_of_padded_coefficient_convergence`
完全一致，直接消费即可，无需新证明尾界 API。

### B5. 两个必须防止的错误推断

1. **偶数幂和不识别符号。** 单项谱 \((1)\) 与 \((-1)\) 的所有偶数幂和相等，但对应的中心化卡方极限互为反射。B1 需要所有 \(q\ge0\) 的测度矩，因而需要原谱的全部 \(k\ge2\) 幂和。
2. **逐坐标收敛不消除尾部质量。** 取长度 n、每项 \(1/\sqrt n\) 的数组，补零后的每个坐标趋于0，但总平方和恒为1。B4 必须使用总平方和趋于目标平方和，不能只使用有界性。这个例子也说明仅高于二阶的幂和不足以排除额外的 Gaussian 极限成分。

## C. `IsSecondChaosSeriesLaw` 的每一个字段

### C1. 先选择概率空间，再定义 Q

对任意 \(\lambda\in\ell^2\)，取

\[
\Omega=\mathbb R^{\mathbb N},\quad
P=\bigotimes_{j\ge0}N(0,1),\quad Z_j(x)=x_j.
\]

当前 mathlib 可用 `Measure.infinitePi`、`Measure.infinitePi_map_eval` 和
`ProbabilityTheory.iIndepFun_infinitePi` 构造概率测度、坐标边际及独立性。

不得声称“在任意预先给定的概率空间上都存在这组独立 Gaussian”。例如单点概率空间不可能承载非退化 Gaussian。最终先证明存在一个携带 Q 的概率空间；如需以 \(\mathbb R\) 为底空间表达极限律，再对 Q 取推前测度。

### C2. L² 部分和收敛及精确尾方差

令 \(X_j=\lambda_j(Z_j^2-1)\)、\(S_N=\sum_{j<N}X_j\)。由独立性及标准 Gaussian 的二阶、四阶矩，

\[
EX_j=0,\qquad E(X_iX_j)=0\ (i\ne j),\qquad EX_j^2=2\lambda_j^2.
\]

现有 `iid_standardGaussian_centeredSquare_finset_L2` 已证明有限和等距公式，故

\[
\|S_M-S_N\|_{L^2(P)}^2=2\sum_{j=N}^{M-1}\lambda_j^2\to0.
\]

\(L^2(P)\) 完备性给出等价类极限 \(Q_2\)。选可测代表 Q；对固定 N 由范数连续性，

\[
E(Q-S_N)^2=2\sum_{j\ge N}\lambda_j^2.                        \tag{C1}
\]

Q 与每个 \(Q-S_N\) 属于 L²。这填好了 `MemLp` 和尾误差积分趋零字段，但还未给出全序列的几乎处处收敛。

### C3. 全序列 a.e. 收敛：有限最大不等式的直接证明

这一步可以用现有 L² 有界鞅收敛定理；若过滤和鞅接口接入成本高，下面给出不依赖鞅 API 的完整证明。

对独立、中心化、平方可积的 \(X_j\)，固定 N<M，令
\(T_k=\sum_{j=N}^{k-1}X_j\)。定义第一次越过阈值 \(\varepsilon>0\) 的不交事件

\[
A_k=\{|T_k|\ge\varepsilon\}\cap
\bigcap_{N\le l<k}\{|T_l|<\varepsilon\},\quad N<k\le M.
\]

\(A_k,T_k\) 只依赖前 k 个坐标，\(T_M-T_k\) 独立于它们且均值为0，所以

\[
E[\mathbf1_{A_k}T_M^2]
=E[\mathbf1_{A_k}T_k^2]+E[\mathbf1_{A_k}(T_M-T_k)^2]
\ge\varepsilon^2P(A_k).
\]

对 k 求和，得

\[
P\!\left(\max_{N\le k\le M}|S_k-S_N|\ge\varepsilon\right)
\le\frac{\sum_{j=N}^{M-1}EX_j^2}{\varepsilon^2}.              \tag{C2}
\]

先以事件的递增并令 \(M\to\infty\)，得到同样的全尾上确界界。选择严格递增 \(N_l\ge l\)，使
\(\sum_{j\ge N_l}EX_j^2\le2^{-4l}\)，取 \(\varepsilon_l=2^{-l}\)。由 (C2)，尾波动超过 \(\varepsilon_l\) 的概率至多 \(2^{-2l}\)，可求和。第一 Borel–Cantelli 引理因此给出：几乎处处，充分大的 l 对所有 \(k\ge N_l\) 都有 \(|S_k-S_{N_l}|<2^{-l}\)。

于是任意 \(k,m\ge N_l\) 时 \(|S_k-S_m|<2^{1-l}\)，故整个实数列 \((S_N)\) 几乎处处 Cauchy，收敛至有限极限 \(Q_*\)。全尾事件的“上确界达到阈值”可改成“存在 k 达到阈值”的可数并，或先使用严格阈值；不要在上确界未达到时擅自选择越界时刻。

部分和同时 L² 收敛到 C2 的 Q，故依概率收敛到 Q；几乎处处收敛也给依概率收敛。依概率极限唯一性推出 \(Q_*=Q\) 几乎处处。因此 C2 中的可测代表具有要求的全序列 a.e. 收敛。

第一 Borel–Cantelli 不要求各越界事件独立；独立性只用在 (C2) 的交叉项消失。若使用鞅路线，先核对 `Submartingale.exists_ae_tendsto_of_bdd` 的过滤、适应性、可积性和一致界，不能只凭“这是鞅”跳过实例化。

### C4. 逐字段输出及不变性

现在可输出仓库的 `IsSecondChaosSeriesLaw P Q λ`：

| 字段 | 证明来源 |
|---|---|
| `AEMeasurable Q P` | L² 代表的可测性 |
| `Summable (fun j => λ j ^ 2)` | A6 或泛型输入 |
| 可测、独立且每个坐标推前为 `gaussianReal 0 1` 的 Z | C1 |
| 每个 \(Q-S_N\) 属于 L² | C2 |
| 平方误差积分趋零 | (C1) |
| 整个部分和序列 a.e. 趋于 Q | C3 |

可以直接用 B3 的交错有符号 \(\lambda\) 来构造 Q。这样不必先为另一种编号构造 Q，再补一整套无限随机级数重排不变性证明。

## D. 消费已有谱截断定理，回到实际 Gaussian 行

### D1. 排列与补零保持有限 Gaussian 二次和的分布

对任意有限实系数行 a，独立标准 Gaussian 的坐标置换保持联合分布，故置换 a 不改变 \(\sum_i a_i(Z_i^2-1)\) 的分布。已有 `centeredSpectralSquares_permute_identDistrib` 提供这一部分。

向系数行插入零也不改变分布：在更大的独立 Gaussian 向量上，原坐标子向量仍为原维数的标准 Gaussian，新增坐标乘零后逐点消失。用有限子坐标的推前概率律证明，不要通过“两个随机变量方差相等”推出同律。

B3 的 v 行是原 a 行加 \(m_n\) 个零后的一次置换。因此

\[
\sum_{i<m_n}a_{n,i}(Z_i^2-1)
\overset d=\sum_{j<2m_n}v_{n,j}(Z_j^2-1).                   \tag{D1}
\]

这应成为一个独立的小 Lean 引理，不必修改实际观测模型的维数。

### D2. 泛型有符号幂和消费定理

给定 (B0)、\(m_n\to\infty\)、A6/C4 构造的 \(\lambda,P,Q\)，B3 给出 v 的补零逐坐标收敛，B4 给出误差函数 e。直接应用现有

`centeredSpectralSquares_tendsto_secondChaos_of_padded_l2`

于行长 \(2m_n\) 和系数 v，得到右侧 (D1) 向 Q 的分布收敛；再由 D1 转回原 a 行。

**无须重写该概率定理。** 它的 `lambdaN` 和 `lambda` 都允许有符号系数，不要求 `Antitone`，不要求非负。真正缺的是 B1–B3 的确定性排序桥、D1 的补零同律和 C4 的极限律构造。

也可直接验证共同概率空间上的 L² 耦合：

\[
\sum_j(v_{n,j}-\lambda_j)^2\to0,
\quad E\left|\sum_j(v_{n,j}-\lambda_j)(Z_j^2-1)\right|^2\to0.
\]

第一个极限由固定前缀收敛和尾界
\(\sum_{j\ge K}(v_{n,j}-\lambda_j)^2\le2\sum_{j\ge K}v_{n,j}^2+2\sum_{j\ge K}\lambda_j^2\)
推出。这是对已有截断定理的独立数学核查，不要求实现第二套并行版本。

### D3. 有限 Gaussian 对角化与最终同律转移

文件22 W2 保证实际活动行最终非退化。对这些行，实际相关矩阵 \(C_n\) 半正定，且每个对角元为1。即使 \(C_n\) 奇异，\(Y_n\overset d=C_n^{1/2}Z\) 仍成立：均值与协方差确定 Gaussian 向量的分布，不需要逆矩阵。

于是实际二阶项等于自伴矩阵 \(B_n\) 的中心化 Gaussian 二次型，正交对角化给其系数行 \(a_{n,i}=\lambda_{n,i}\)。文件22 W5 提供 (B0)，本文件 A6 提供目标谱、C4 提供 Q，D2 即给实际二阶项收敛。

当前可复用 `gaussianLogQuadraticStatistic_identDistrib_eigenvalueSquares`。如果现有最终消费接口仍要求所有 n 的非退化性，不要传入假前提；只在最终事件上应用该逐行同律定理。对任何有界连续测试函数，实际行与谱行的期望最终相同，故其极限相同。也可安全补齐前面有限行，再使用 `DistributionVaryingLawTransfer.lean` 的工具；这里真正需要的是**最终同律**，不是两种不同样本空间上逐点相等。

完成 D3 后才可消除最终定理中的 `hRiesz`、`hQ`、`hwnn`、`hNegMass` 及全行 `hane`。W8–W9 的实际 log 和估计器传递接着按文件22与[文件24](24_endpoint_and_validation_contracts.md)处理。

## E. 后续非 Gaussian 性与特征函数：不借助未证的矩交换

### E1. 四阶矩公式和 L⁴ 尾收敛

L² 收敛本身不能推出四阶矩收敛。对有限部分和 \(S_N=\sum_{j<N}\lambda_j(Z_j^2-1)\)，Gaussian 多项式矩及独立性给

\[
ES_N^2=2\sum_{j<N}\lambda_j^2,\quad
ES_N^3=8\sum_{j<N}\lambda_j^3,
\]
\[
ES_N^4=12\left(\sum_{j<N}\lambda_j^2\right)^2
       +48\sum_{j<N}\lambda_j^4.                            \tag{E1}
\]

第四式的展开只保留全相同指标或两两相同指标：标准化 \(Z^2-1\) 的二阶矩为2、三阶矩为8、四阶矩为60；所以全相同项系数为60，两两相同项为 \(6\cdot2\cdot2=24\)。合并成 (E1)。标准 Gaussian 的所需偶数矩可用分部积分递推 \(EZ^{2k}=(2k-1)EZ^{2k-2}\) 从 \(EZ^0=1\) 得到。

对 \(S_M-S_N\) 使用同一公式，记 \(t_N=\sum_{j\ge N}\lambda_j^2\)，则

\[
E|S_M-S_N|^4\le12t_N^2+48t_N^2=60t_N^2\to0.
\]

故部分和在 L⁴ 中 Cauchy，L⁴ 极限因依概率极限唯一性仍为 Q。因此 (E1) 可令 N 趋于无穷，得到 Q 的二、三、四阶矩；这一步具有明确的一致可积性依据。

若 \(\lambda\ne0\)，则第四累积量

\[
EQ^4-3(EQ^2)^2=48\sum_j\lambda_j^4>0,
\]

而中心 Gaussian 的该量为0，所以 Q 非 Gaussian。Riesz 情形 \(\lambda\ne0\) 来自文件22 W10 的严格正性证明：\(\int\omega=1\) 保证 \(\omega\ne0\)，Laplace 平方表示给 \(J_2>0\)。不能只用 \(J_2\ge0\) 推出非退化。

### E2. 单个中心化 Gaussian 平方的全实轴特征函数

对实系数 a，令 \(f_a(u)=E e^{iua(Z^2-1)}\)。有

\[
f_a(u)=\exp\left[-iua-\tfrac12\operatorname{Log}(1-2iua)\right],
\qquad u\in\mathbb R.                                      \tag{E2}
\]

无需把复杂 Gaussian 积分公式作为新假设，可直接证明：记 \(g(u)=Ee^{iuaZ^2}\)。Gaussian 分部积分应用于 \(x e^{iua x^2}\)，得到
\((1-2iua)E[Z^2e^{iuaZ^2}]=g(u)\)。边界项由 Gaussian 密度的衰减趋零，导数项的绝对值受常数乘 \(1+x^2\) 控制，故可积。

对 u 求导可用 \(|a|(Z^2+1)\) 控制。于是

\[
f_a'(u)=\frac{-2ua^2}{1-2iua}f_a(u),\qquad f_a(0)=1.
\]

(E2) 右侧在 \(1-2iua\) 的实部恒为1的路径上可微，满足同一个微分方程且从不为零。对两者之商求导得到0，再用 u=0 的值即可。选择右半平面上的主对数，不得随 u 任意更换平方根分支。

### E3. 无限级数的全实轴公式与局部幂级数范围

记 \(\ell_a(u)=-iua-\tfrac12\operatorname{Log}(1-2iua)\)。由上面的导数及 \(|1-2iua|\ge1\)，

\[
|\ell_a(u)|
\le\int_0^{|u|}2t a^2dt=u^2a^2.                            \tag{E3}
\]

所以 \(\sum_j\ell_{\lambda_j}(u)\) 对每个实 u 绝对收敛，且在任意紧 u 区间上一致收敛。有限独立性及 (E2) 给出部分和特征函数
\(\varphi_{S_N}(u)=\exp\sum_{j<N}\ell_{\lambda_j}(u)\)。又由 C2

\[
|\varphi_Q(u)-\varphi_{S_N}(u)|
\le |u|E|Q-S_N|\le |u|\sqrt{2t_N}\to0.
\]

因此全实轴公式为

\[
\varphi_Q(u)=\exp\sum_j\ell_{\lambda_j}(u).                  \tag{E4}
\]

只有当 \(2|u|D<1\)、\(D\ge\sup_j|\lambda_j|\) 时，才能再展开每一项的对数并交换 j、k 两个级数。合法性由

\[
\sum_{k=2}^\infty\frac{2^{k-1}|u|^k}{k}
\sum_j|\lambda_j|^k
\le\left(\sum_j\lambda_j^2\right)
\sum_{k=2}^\infty\frac{2^{k-1}|u|^kD^{k-2}}{k}<\infty
\]

保证，得到 \(\log\varphi_Q(u)=\frac12\sum_{k\ge2}(2iu)^kJ_k/k\) 的零点邻域版本。此处 \(\log\varphi_Q\) 指由右侧连续选定、在零点取0的对数，不应在全实轴任意改成另一个主值对数。

这些公式用于验证极限的性质；D2 的分布收敛已经由谱截断证明，不依赖先实现复分析矩唯一性。

## F. API 核对表与停止扩张的边界

以下名称在当前源码中已查到；表中只承诺“存在且用途相符”，不表示新的调用已编译。

| 位置 | 已核对声明或内容 | 接手时的用途 |
|---|---|---|
| `Mathlib.Analysis.InnerProductSpace.Spectrum` | `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`、`finite_dimensional_eigenspace` | 紧自伴谱分解的底层依据；可数编号仍需组装 |
| `Mathlib.Topology.ContinuousMap.StoneWeierstrass` | 多项式/代数一致逼近基础 | B1 连续测试函数逼近；不要猜测具体重载参数 |
| `Mathlib.Probability.ProductMeasure` | `Measure.infinitePi`、`Measure.infinitePi_map_eval` | Gaussian 可数乘积及边际 |
| `Mathlib.Probability.Independence.InfinitePi` | `iIndepFun_infinitePi` | 坐标独立性 |
| `Mathlib.Probability.Martingale.Convergence` | `Submartingale.exists_ae_tendsto_of_bdd` | C3 的可选现成 a.e. 收敛入口 |
| `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli` | `MeasureTheory.measure_limsup_atTop_eq_zero` | C3 直接最大不等式路线的第一 Borel–Cantelli |
| `Hurst.SecondChaosSeriesL2` | `iid_standardGaussian_centeredSquare_finset_L2` | C2 有限和等距公式 |
| `Hurst.SpectralMatchingSort` | `decreasingSpectralPerm`、`decreasingSpectralPerm_antitone` | 正负部分分别排序 |
| `Hurst.SpectralMatchingTail` | `spectralTailBound_of_padded_coefficient_convergence` | B4，不要求谱非负 |
| `Hurst.SpectralPermutation` | `centeredSpectralSquares_permute_identDistrib` | D1 的排列部分 |
| `Hurst.FiniteSpectralArrayConvergence` | `centeredSpectralSquares_tendsto_secondChaos_of_padded_l2` | D2 的主要概率消费接口 |
| `Hurst.FeatureQuadraticSpectral` | `gaussianLogQuadraticStatistic_identDistrib_eigenvalueSquares` | D3 实际行的谱表示 |

实现前用 `#check`/`#print` 核对具体隐式参数和命名空间；不要从名字相似推断定理适用。A3 的 HS 工具目前尚未找到一套可以直接整体调用的现成接口，因此列出了足够的专用证明，不以“mathlib 应该有”隐藏这部分工作。

本次已运行[接口核对文件](../verification/LongMemoryHandoffAPICheck.lean)，16 个 `#check` 全部通过，进程退出码为0。该文件没有新增数学定理，也没有验证本文件的新组合。可从项目根目录复现：

```sh
/Users/jinqishen/.elan/bin/lake env lean verification/LongMemoryHandoffAPICheck.lean
```

本文件不要求重建完整 Schatten 理论、一般迹类算子库、通用矩母函数收敛理论或新的无限维 Weyl 不等式。若实现需要转向这些大型支线，应先检查是否已经偏离上述可复用接口；数学上可替代，不代表对本项目的形式化成本合适。
