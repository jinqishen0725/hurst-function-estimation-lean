# 11. 一维二阶差分：实际非恒定 H 的短记忆 CLT

对应：Theorem 3.3 的 d=1、q=2 分支，Theorem 3.4 的反演极限及偏差，Corollary 3.5 的修正均值；复用 8.2、8.3、8.4，并补足本分支所需的三角阵列概率论。

**状态：在文件10的内部区间、已知尺度、p≥2条件下，以下普通数学证明闭合。** 不假设输入 CLT，不以平稳近似作为未证前提。最优带宽的具体非零均值另要求第6节的点态 Taylor 展开。尚未转 Lean；q=1、临界、长记忆及未知尺度分支不在本文件范围内。

## 1. 结论和极限方差

沿用[文件10](10_q2_mbm_mse.md)全部记号。固定目标点 \(t\in I\)，令 \(h=H(t)\)，\(N=nb\)，\(L=\log n\)。局部多项式的等价核为

\[
A(z)=(1,z,\ldots,z^m)^\top,\quad
M=\int K(z)A(z)A(z)^\top\,dz,\quad
\omega(z)=K(z)e_0^\top M^{-1}A(z).
\]

文件02已从真实网格推出 \(M\) 正定、\(\int\omega=1\)，以及

\[
f_{n,i}:=Nw_i(t)=\omega((t_i-t)/b)+O(N^{-1})\mathbf1_{\{|t_i-t|\le b\}}.
                                                                    \tag{11.1}
\]

令 \(r_h(k)=g_2(h,k)/v(h)\)，其中 \(v(h)=4-2^{2h}\)。写

\[
g(z)=\log z^2-\mu_0=\sum_{\ell\ge2,\ \ell\ \mathrm{even}}b_\ell H_\ell(z),
\]

\[
\tau_h^2=\sum_{k\in\mathbb Z}
 \sum_{\ell\ge2,\ \ell\ \mathrm{even}}b_\ell^2\ell!\,r_h(k)^\ell,
\qquad V(t)=\tau_h^2\int\omega(z)^2\,dz.                            \tag{11.2}
\]

该双和绝对收敛且 \(0<V(t)<\infty\)：\(|r_h(k)|\le C(1+|k|)^{-2-2\eta}\)，各偶数阶项非负，k=0 的项是 \(Eg(Z)^2>0\)，且 \(\int\omega=1\)。以下证明

\[
\sqrt{nb}\{\widehat G_n(t)-E\widehat G_n(t)\}
 \Rightarrow N(0,V(t)),                                            \tag{11.3}
\]

\[
2\sqrt{nb}L\{\widehat H_n(t)-T_n(E\widehat G_n(t))\}
 \Rightarrow N(0,V(t)).                                            \tag{11.4}
\]

(11.4) 也可把中心改成 \(E\widehat H_n(t)\)，见第5节。一般反演极限仍有负号；这里只有中心正态的对称性使分布相同。

## 2. 实际相关阵列的局部极限与方差

文件10已经对实际 \(Y_i=D_i/\sqrt{\operatorname{Var}D_i}\) 证明

\[
|r_n(i,j)|\le C(1+|i-j|)^{-2-2\eta},\qquad
\sup_{n,i}\sum_j|r_n(i,j)|\le C.                                  \tag{11.5}
\]

对每个固定整数 k，其有界滞后近似(10.8)给出

\[
\sup_{i:\ |t_i-t|\le b}
 |r_n(i,i+k)-r_h(k)|\longrightarrow0.                              \tag{11.6}
\]

理由是 \(H(t_i),H(t_{i+k})\to H(t)\) 一致、冻结 g 连续、误差 \(O_k(L/n)\)，且实际方差有一致正下界。仅对有效基点书写；所有有非零权重的点及其固定 k 邻点最终有效。

由(11.1)和移位 Riemann 和，对每个固定 k，

\[
\frac1N\sum_i f_{n,i}f_{n,i+k}\longrightarrow\int\omega^2.          \tag{11.7}
\]

于是 \(S_n=N^{-1/2}\sum_i f_{n,i}g(Y_i)\) 的方差可以按 k 分组。每个 k 的绝对贡献由

\[
C(1+|k|)^{-4-4\eta}\sum_\ell b_\ell^2\ell!
\]

控制，因 \(f_{n,i}\) 一致有界且支集含 \(O(N)\) 个点。对 k 使用可求和控制，对 Hermite 阶数使用 \(\sum b_\ell^2\ell!<\infty\)，再由(11.6)–(11.7)取极限，得到

\[
\operatorname{Var}S_n\longrightarrow V(t).                         \tag{11.8}
\]

相同结论对任意有限 Hermite 截断成立，其方差极限记作 \(V_K(t)\)。

## 3. 有限 Hermite 多项式的 CLT：连通图直接证明

令 \(P_K(z)=\sum_{2\le\ell\le K,\ \ell\ \mathrm{even}}b_\ell H_\ell(z)\)，\(S_{n,K}=N^{-1/2}\sum_i f_{n,i}P_K(Y_i)\)。固定 K，证明它趋于 \(N(0,V_K(t))\)。

先说明使用的组合恒等式。对任意 r 个 Gaussian 变量，生成函数满足

\[
E\prod_{a=1}^r e^{u_aY_{i_a}-u_a^2/2}
 =\exp\left(\sum_{a<c}r_n(i_a,i_c)u_a u_c\right).
\]

比较单项式系数，可把 \(E\prod_a H_{\ell_a}(Y_{i_a})\) 写成有限多重图之和：顶点 a 的度为 \(\ell_a\)，没有自环，每条 a–c 边贡献 \(r_n(i_a,i_c)\)，另乘仅依赖各阶数和边重数的组合系数。这里顶点是因子的位置，即使 \(i_a=i_c\) 也仍是两个顶点，恒等式不变。

r 阶联合累积量按定义为

\[
\kappa(U_1,\ldots,U_r)
 =\sum_{\pi\ \text{为}\ [r]\text{的分割}}
 (|\pi|-1)!(-1)^{|\pi|-1}\prod_{B\in\pi}E\prod_{a\in B}U_a.
\]

把上述图展开代入。一个图若有 c 个连通分量，它在这个和中的总乘数为
\(\sum_{j=1}^c S(c,j)(j-1)!(-1)^{j-1}\)，c=1 时为1，c>1 时为0。该恒等式可由形式幂级数 \(\log(e^x)=x\) 比较 \(x^c/c!\) 的系数得到。因此仅连通图保留。这个证明只涉及多项式矩，不要求多项式随机变量的矩母函数在零附近存在。

每个连通图选取一棵生成树。由 \(|r_n|\le1\)，图对应乘积的绝对值不超过树边相关系数绝对值之积。先对树根的下标求和，共 \(O(N)\) 个有权重点；再按叶子逐个求和，每一步由(11.5)至多产生常数 C。权重 f 一致有界，所以每个图的带权下标和为 \(O(N)\)。固定 r、K 时图数和组合系数有限，故

\[
|\kappa_r(S_{n,K})|\le C_{r,K}N^{1-r/2},\qquad r\ge3.              \tag{11.9}
\]

一阶累积量为0，二阶由第2节趋于 \(V_K(t)\)。矩与累积量的分割公式因此表明 \(S_{n,K}\) 的所有整数阶矩趋于对应 Gaussian 矩。二阶矩有界给出紧性，更高偶数阶矩有界使任意子列极限继承全部矩。这里矩唯一性也可直接验证：任何具有该 Gaussian 矩序列的子列极限 U，由 Tonelli 得 \(E\cosh(aU)=\exp(a^2V_K/2)\)，故 \(Ee^{a|U|}<\infty\)。特征函数的幂级数于是可以与期望交换，并由相同矩得到 Gaussian 特征函数。因此所有子列极限都相同。于是

\[
S_{n,K}\Rightarrow N(0,V_K(t)).                                   \tag{11.10}
\]

这处理了非平稳相关矩阵和真实离散权重，并未调用一个尚未验证适用条件的平稳 CLT。

## 4. 从多项式到对数

令 \(R_K=g-P_K\)。正交展开以及(11.5)给出

\[
\begin{aligned}
E|S_n-S_{n,K}|^2
&\le\frac1N\sum_{i,j}|f_{n,i}f_{n,j}|r_n(i,j)^2
       \sum_{\ell>K}b_\ell^2\ell!\\
&\le C\sum_{\ell>K}b_\ell^2\ell!\longrightarrow0,
\end{aligned}                                                       \tag{11.11}
\]

一致于 n。并且 \(V_K(t)\to V(t)\)。例如对任意有界1-Lipschitz测试函数，(11.11)控制 S 与截断之差，(11.10)给出固定 K 的极限，再令 K 趋于无穷；即得(11.3)。对数在零附近的奇异性没有被略去，它已由 Gaussian \(L^2\) 展开及一致尾界处理。

## 5. 反演、真实期望中心和精细偏差

记 \(\mu_n=E\widehat G_n(t)\)，\(\theta_n=T_n(\mu_n)\)，\(B_n=\mu_n-G_n(H(t))\)。文件10给出 \(|B_n|\le CL(b^p+n^{-1})=o(L)\)，故 \(\theta_n\to H(t)\)，最终处于固定的内部 H 紧区间，截断不在 \(\mu_n\) 附近发生。

在文件01的反演线性化中取 \(a_n=\sqrt{nb}\)，\(\ell\) 为本模型的光滑函数。输入条件现已由(11.3)及文件10验证。因此

\[
2\sqrt{nb}L(\widehat H_n-\theta_n)
 +\sqrt{nb}(\widehat G_n-\mu_n)\longrightarrow_P0,                 \tag{11.12}
\]

从而得到(11.4)。

还可以补齐同一范围的偏差控制，而不另假设对数统计量的高阶尾界。令 \(e_n=\widehat G_n-\mu_n\)，其均值为0、方差 \(V_n\le C/N\)。在 \(|e_n|\le cL\) 上选择固定小 c，使逆像留在内部 H 紧区间。该处逆函数的二阶导数满足

\[
|(G_n^{-1})''|=\frac{|\ell''|}{|G_n'|^3}\le C/L^3.
\]

Taylor 余项因此不超过 \(Ce_n^2/L^3\)。在补集上，用截断逆的全局 \(1/(2L)\)-Lipschitz 性及 \(|(G_n^{-1})'(\mu_n)|\le1/(2L)\)，去掉线性项后的绝对误差不超过 \(|e_n|/L\)。由

\[
E[|e_n|\mathbf1_{\{|e_n|>cL\}}]\le V_n/(cL)
\]

得到

\[
|E\widehat H_n-\theta_n|\le C V_n/L^2\le C/(NL^2).                \tag{11.13}
\]

故 \(2\sqrt N L(E\widehat H_n-\theta_n)\to0\)，(11.4) 可改用真实期望中心。

另一方面，由 \(G_n(\theta_n)-G_n(H(t))=B_n\) 和 \(\ell'\) 一致有界，

\[
\theta_n-H(t)=-\frac{B_n}{2L}+O(|B_n|/L^2).
\]

结合(11.13)，还证明了实际偏差公式

\[
E\widehat H_n(t)-H(t)
 =-\frac{E\widehat G_n(t)-G_n(H(t))}{2\log n}
   +O\left(\frac{|B_n|+(nb)^{-1}}{\log^2n}\right).                 \tag{11.14}
\]

因此本分支不只是 MSE 传递，精细的一阶偏差反演也已接上实际模型。

## 6. 最优带宽下，推论3.5的两个均值

本节加：p为整数，H在固定 t 处有 p 阶 Peano Taylor 展开，例如 \(H\in C^p\) 于 t 的邻域。局部多项式次数仍为 p−1。设

\[
R_H(t)=\frac{H^{(p)}(t)}{p!}\int z^p\omega(z)\,dz.
\]

文件02的实际网格首项展开及文件10的对数均值逼近给出

\[
B_n=-2Lb^pR_H(t)+o(Lb^p)+O(L/n).                                  \tag{11.15}
\]

这里 \(\ell\circ H\) 的平滑偏差为 \(O(b^p)=o(Lb^p)\)；若 \(R_H(t)=0\)，(11.15) 仍是合法的加法展开，无需对0使用等价记号。

令 \(b_0=(nL^2)^{-1/(2p+1)}\)、\(b/b_0\to c\in(0,\infty)\)，以及

\[
A_n=(n^p/L)^{1/(2p+1)}=\sqrt{nb_0}.
\]

有 \(A_nLb_0^p=1\)、\(1/n=o(b_0^p)\)。因此(11.3)和(11.15)推出

\[
A_n\{\widehat G_n(t)-G_n(H(t))\}
 \Rightarrow N(-2c^pR_H(t),\ c^{-1}V(t)).                           \tag{11.16}
\]

再由(11.12)和 \(\theta_n-H=-B_n/(2L)+O(|B_n|/L^2)\)，

\[
2(nL^2)^{p/(2p+1)}\{\widehat H_n(t)-H(t)\}
 \Rightarrow N(2c^pR_H(t),\ c^{-1}V(t)).                            \tag{11.17}
\]

所以 c=1 时原推论印出的两个 R 均值须分别改成 **−2R 和 +2R**。文件01此前证明的是条件传递；这里对 d=1、q=2 的实际非恒定 H 估计量补齐了其所有输入。

## 7. 本次结论的边界

- 已完成：固定内部点、一维二阶差分的短记忆 CLT、反演负号、真实期望中心、精细偏差传递，以及有点态 Taylor 首项时的最优带宽修正正态极限。
- 与文件10合起来，已完成这一分支的真实模型 → 协方差 → 对数矩 → 平滑偏差/方差 → MSE → CLT 链。
- 未宣称完成：原 Theorem 3.3 的所有维度和记忆分支、q=1 的临界/长记忆极限、未知尺度两尺度联合问题、空间平均、边界与非规则网格，也未宣称完成 Lean 形式化。
