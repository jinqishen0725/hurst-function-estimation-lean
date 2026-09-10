# 15. 未知尺度的两尺度 pilot：真实联合协方差与极限

对应：Theorem 4.1；复用8.2、8.3、8.4及S.3的概率论。本文件处理d=1、q=1或q=2；q=1要求p≥1，q=2要求p≥2。其余光滑性、H紧区间、非零非负紧支撑C¹核、固定内部区域均沿用文件10/12。尺度σ未知但为固定正常数。

**状态：本文件所列一维内部范围的普通数学证明闭合，尚未转Lean。** 两个尺度使用同一批有效基点、同一带宽b₁和同一实际局部多项式权重；没有把方向加倍错误地当成独立样本，或直接替换为n/2个观测。

## 1. 实际估计量与结论

令 \(a\in\{1,2\}\)、\(d_j=(-1)^j\binom qj\)，在有效基点 \(i\le n-2q\) 上定义

\[
D_{i,a}=\sum_{j=0}^q d_jX(t_i+aj/n),\quad
G_a^{\wedge}(t)=\sum_iw_i(t)\log D_{i,a}^2,
\quad P(t)=\frac{G_2^{\wedge}(t)-G_1^{\wedge}(t)}{2\log2}.
\]

\(w_i(t)\) 使用带宽b₁，\(N=nb_1\)、\(L=\log n\)、\(b_1\to0,N\to\infty,b_1L\to0\)。固定t，记 \(h=H(t)\)、\(\psi=2q-2h\)，并定义

\[
\rho_{q,n}(t)=
\begin{cases}L/n+n^{-\psi},&q=1,\\L/n,&q=2.\end{cases}
\]

本文件证明

\[
|EP(t)-H(t)|\le C(b_1^p+\rho_{q,n}(t)),\qquad
\operatorname{Var}P(t)\le C T_\psi(N),                             \tag{15.1}
\]

其中T为文件12的三分支方差函数。q=2始终短记忆。短记忆和临界时得到非退化的中心正态极限；q=1长记忆时还可得到实际非正态极限。

## 2. 两尺度的真实协方差

定义冻结交叉协方差

\[
g_{ab}(h,k)=-\tfrac12\sum_{r,s=0}^q d_rd_s|k+bs-ar|^{2h},
\quad v_q(h)=g_{11}(h,0),
\quad R_{ab}(h,k)=\frac{g_{ab}(h,k)}{a^hb^h v_q(h)}.               \tag{15.2}
\]

这里 \(v_1(h)=1\)、\(v_2(h)=4-2^{2h}\)。令 \(Y_{i,a}=D_{i,a}/\sqrt{\operatorname{Var}D_{i,a}}\)。从文件10/12的真实协方差证明，可得到：

1. 每个固定有界滞后k，原始归一化协方差满足
\[
\sigma^{-2}n^{H(t_i)+H(t_{i+k})}\operatorname{Cov}(D_{i,a},D_{i+k,b})
 =g_{ab}(H(t_i),k)+O(\rho_{q,n}(t)),                              \tag{15.3}
\]
在目标窗口中一致；尤其实际方差为 \(a^{2H(t_i)}v_q(H(t_i))+O(\rho_{q,n}(t))\)，有一致正下界。

2. 同一窗口中，实际标准化相关系数满足
\[
|r_n(i,a;j,b)|\le C(1+|i-j|)^{-\psi(t)}.                          \tag{15.4}
\]
工作区间的全局版本可将ψ换成 \(\bar\psi=2q-2\sup_JH\)。

3. q=1、\(k=|i-j|\to\infty\)、\(k\le Cnb_1\) 时，
\[
r_n(i,a;j,b)
 =\left\{c(ab)^{1-h}+O(k^{-1}+\varepsilon_n)\right\}k^{-\psi},
\quad c=h(2h-1),\quad
\varepsilon_n=b_1L+b_1^\psi+\rho_{1,n}(t)\to0.                   \tag{15.5}
\]

这些不是额外输入假设。具体推导如下：(15.3)对实际有限和逐项使用H端点变化 \(O(1/n)\) 和文件10/12的背景差分界；a,b均固定，所有常数一致。(15.4)把q次长度a/n和q次长度b/n的差分写成2q重导数积分，使用已证明的混合导数界，再除以实际标准差。对(15.5)，同样积分中的冻结主系数为 \(c ab\)，标准化后为 \(c(ab)^{1-h}\)。移位差的均值在a≠b时未必为0，因此有限滞后相对误差只取 \(O(k^{-1})\)，不能直接套用同尺度的 \(O(k^{-2})\)；冻结H和光滑背景误差同文件12。这些推导同时允许交叉相关不关于k对称，只要求 \(R_{ab}(h,k)=R_{ba}(h,-k)\)。

## 3. pilot偏差与方差

Gaussian缩放及(15.3)给

\[
E\log D_{i,a}^2=\log\sigma^2-2LH(t_i)+2H(t_i)\log a
                +\log v_q(H(t_i))+\mu_0+O(\rho_{q,n}(t)).
\]

两尺度相减时，尺度、L项、log v和Gaussian对数常数逐点消去。因此

\[
EP(t)=\sum_iw_i(t)H(t_i)+O(\rho_{q,n}(t)).
\]

实际权重精确再现给(15.1)的偏差。随机部分是 \(g(Y_{i,2})-g(Y_{i,1})\) 的加权和，\(g(z)=\log z^2-\mu_0\)。对所有尺度组合，Hermite恒等式给
\(|\operatorname{Cov}(g(Y_{i,a}),g(Y_{j,b}))|\le Eg(Z)^2 r_n(i,a;j,b)^2\)。代入(15.4)及权重界即得方差(15.1)。不使用两尺度独立性。

## 4. 短记忆联合CLT与非退化pilot方差

若 \(2\psi>1\)，则

\[
\sqrt N\begin{pmatrix}G_1^{\wedge}-EG_1^{\wedge}\\G_2^{\wedge}-EG_2^{\wedge}\end{pmatrix}
 \Rightarrow N_2(0,\Gamma(h)\int\omega^2),
\]

\[
\Gamma_{ab}(h)=\sum_{k\in\mathbb Z}\sum_{\ell\ge2,\ \ell\text{偶}}
 b_\ell^2\ell!\,R_{ab}(h,k)^\ell.                                \tag{15.6}
\]

证明可直接复用文件13的连通单环图界：把下标扩成(i,a)，总数仍为O(N)，绝对行和与平方行和至多增加固定因子2。固定滞后的实际相关趋于(15.2)，绝对平方衰减可求和，故得到每个线性组合的方差极限。有限Hermite截断、累积量消失及一致L²尾界均照此成立。Cramér–Wold给联合CLT。

从而

\[
\sqrt N(P-EP)\Rightarrow N(0,V_P),\quad
V_P=\frac{\Gamma_{22}+\Gamma_{11}-2\Gamma_{12}}{4\log^22}\int\omega^2>0.
                                                                    \tag{15.7}
\]

下面验证严格正性，避免只声称一个可能退化的正态极限。冻结的一阶尺度、q阶差分序列的谱密度为

\[
f_h(\lambda)=\frac{\pi}{D(h)^2v_q(h)}|1-e^{i\lambda}|^{2q}
 \sum_{m\in\mathbb Z}|\lambda+2\pi m|^{-2h-1},\quad -\pi<\lambda<\pi.
\]

这是将原连续谱积分按2π周期折叠所得，约定 \(R_{11}(h,k)=(2\pi)^{-1}\int e^{ik\lambda}f_h(\lambda)d\lambda\)。它几乎处处严格正，且 \(f_h\in L^2\)，因为零点附近为 \(O(|\lambda|^{\psi-1})\)，而ψ>1/2。

冻结两尺度序列有精确滤波关系 \(Y_{i,2}=2^{-h}(1+E)^qY_{i,1}\)，E表示单位移位。由Parseval，pilot二阶Hermite部分的长期方差为

\[
\frac{2}{2\pi(2\log2)^2}\int_{-\pi}^{\pi}f_h(\lambda)^2
 \{2^{-2h}|1+e^{i\lambda}|^{2q}-1\}^2d\lambda>0.                 \tag{15.8}
\]

括号不是恒零函数。不同Hermite阶正交，每一阶的长期方差非负（是有限加权方差极限），故完整pilot方差不小于此严格正量，再乘 \(\int\omega^2>0\)。这证明(15.7)。

两尺度都使用全部有效网格时，应使用交叉和(15.6)，不能未经证明地把尺度2的长期方差替换为“把样本数n减半”后的方差。

## 5. q=1临界联合CLT

若h=3/4，置 \(V_c=(9/16)\int\omega^2\)。由(15.5)，临界交叉相关主系数为 \((3/8)(ab)^{1/4}\)。文件13的临界双和计算给

\[
\sqrt{N/\log N}
\begin{pmatrix}G_1^{\wedge}-EG_1^{\wedge}\\G_2^{\wedge}-EG_2^{\wedge}\end{pmatrix}
\Rightarrow N_2\left(0,V_c
 \begin{pmatrix}1&\sqrt2\\\sqrt2&2\end{pmatrix}\right).            \tag{15.9}
\]

细节是：相关平方替换误差现在为 \(O(k^{-2}+\varepsilon_n/k)\)，其和除以log N仍趋于0；二阶Hermite项主导；扩成两个尺度的单环图估计仍给高阶累积量趋于0。虽然联合极限秩为1，pilot差值未被消去：

\[
\sqrt{N/\log N}(P-EP)
 \Rightarrow N\left(0,\frac{(\sqrt2-1)^2}{4\log^22}V_c\right).     \tag{15.10}
\]

因此pilot临界时仍有log N的方差损失；差分两个尺度不会自动消除它。

## 6. q=1长记忆的补充联合极限

若h>3/4，\(\psi=2-2h\)，(15.5)及文件14的阶梯算子构造给两尺度块核极限

\[
K_{ab}(x,y)=v_av_b c|x-y|^{-\psi},\qquad v_a=a^{1-h}.
\]

同文件14，对角带的L²质量由2ψ<1控制，离对角线实际核收敛。对任意两个实系数α₁,α₂，二阶混沌算子的非零谱是文件14中A的谱乘以 \(\alpha_1v_1^2+\alpha_2v_2^2\)：因为尺度部分为秩1矩阵vvᵀ，压缩 \(\operatorname{diag}(\alpha)\) 后恰产生这个因子。高阶Hermite尾项仍消失。因此联合极限是

\[
N^\psi(G_1^{\wedge}-EG_1^{\wedge},G_2^{\wedge}-EG_2^{\wedge})
 \Rightarrow (Q,2^\psi Q),
\]

\[
N^\psi(P-EP)\Rightarrow\frac{2^\psi-1}{2\log2}Q.                 \tag{15.11}
\]

这也明确说明长记忆依赖不会因pilot相减而消失。

## 7. 对4.1的修正登记

实际pilot偏差、三种方差率以及短/临界联合CLT均已证明。极限应中心化为P−EP；若改为P−H，须另加入归一化偏差极限。原文的E[H(t)]不能代替EP。两尺度应保留交叉相关，原数据上尺度加倍与重新抽取n/2个样本不应混用。完整高维版本及全边界范围不在本文件结论内。
