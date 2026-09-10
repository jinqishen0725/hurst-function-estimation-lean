# 13. 一阶差分：实际非恒定 H 的短记忆与临界 CLT

对应：Theorem 3.3(i)(ii)、Theorem 3.4、Corollary 3.5 的一维 q=1 部分；S.3.2、S.3.3、S.3.4。以[文件12](12_q1_mbm_covariance_mse.md)的真实协方差估计为基础。

**状态：以下内部点、已知尺度、p≥1、b log n→0范围的普通数学证明闭合，尚未转 Lean。** 临界结论允许 H 在目标点附近非恒定，甚至跨过3/4；不只处理常H子模型。

## 1. 结论

沿用文件12记号，固定目标点 t，\(h=H(t)\)、\(\psi=2-2h\)、\(N=nb\)。由文件02，实际权重满足

\[
f_{n,i}:=Nw_i(t)=\omega(z_i)+O(N^{-1})\mathbf1_{\{|z_i|\le1\}},
\quad z_i=(t_i-t)/b,
\quad \omega(z)=K(z)e_0^\top M^{-1}A(z),\quad \int\omega=1.         \tag{13.1}
\]

\(f_{n,i}\) 一致有界，非零项数为 \(O(N)\)。写
\(g(z)=\log z^2-\mu_0=\sum_{\ell\ge2,\ \ell\text{偶}}b_\ell H_\ell(z)\)，\(b_2=1\)。

**短记忆：** 若 \(h<3/4\)，则

\[
\sqrt N(\widehat G(t)-E\widehat G(t))\Rightarrow N(0,V_h),
\quad
V_h=\left(\sum_{k\in\mathbb Z}\sum_{\ell\ge2,\ \ell\text{偶}}
 b_\ell^2\ell!\,g_1(h,k)^\ell\right)\int\omega^2.                 \tag{13.2}
\]

**临界：** 若 \(h=3/4\)，则

\[
\sqrt{N/\log N}(\widehat G(t)-E\widehat G(t))
 \Rightarrow N\left(0,\frac9{16}\int\omega(z)^2\,dz\right).        \tag{13.3}
\]

两种方差常数严格为正。相同归一化记作 \(a_n\)，则

\[
2a_n\log n(\widehat H(t)-E\widehat H(t))
 \Rightarrow \text{同一中心正态分布}.                              \tag{13.4}
\]

反演在统计量层面取负，正态对称性才使分布相同。

## 2. 相关系数不绝对可求和时的有限 Hermite CLT

文件11用相关系数绝对行和有界来控制生成树。这里需要更强的论证：当 \(1/2<h<3/4\) 时，相关系数可不绝对可求和，只有平方可求和。不能原样复用那个充分条件。

对局部有效下标集合上的真实相关矩阵 R，置

\[
A_N=\max_i\sum_j|r_n(i,j)|,\qquad
B_N=\max_i\sum_j r_n(i,j)^2.
\]

令 P 为固定、中心化、Hermite最低阶至少2的多项式。对固定 \(r\ge3\)，有

\[
\left|\kappa_r\left(\sum_i f_{n,i}P(Y_i)\right)\right|
 \le C_{r,P}N B_N A_N^{r-2}.                                     \tag{13.5}
\]

**证明。** Gaussian Hermite生成函数和累积量的分割消去恒等式，已在文件11第3节直接证明。保留下来的图都是连通、没有自环的多重图，每个顶点的度至少2。因此边数至少顶点数，图含一个环（允许两条平行边组成长度2的环）。选一个环，再接入树枝，得到覆盖全部 r 个顶点、恰含一个环的连通子图。丢弃其他边只会增大相关系数绝对值乘积，因为 \(|r_n|\le1\)。

设环长 m≥2。树枝上逐个消去叶子，每一步至多产生 \(A_N\)，共 r−m 步。环的下标和是 \(\operatorname{tr}(U^m)\)，其中 \(U_{ij}=|r_n(i,j)|\)。U为实对称矩阵，不必正定；其元素非负保证该环和非负，而谱分解给

\[
\operatorname{tr}(U^m)\le\sum_j|\lambda_j(U)|^m
 \le\|U\|_{\rm op}^{m-2}\operatorname{tr}(U^2)
 \le A_N^{m-2}\,C N B_N.
\]

最后一步用对称矩阵的行和界及局部下标数 \(O(N)\)。权重绝对值有界，固定多项式和 r 仅产生有限个图。合并得到(13.5)。这不是假设绝对可求和的平稳定理，而是对当前有限非平稳矩阵的直接界。∎

由文件12的真实相关衰减，

\[
A_N\le C\left(1+\sum_{k\le2N}k^{-\psi}\right),\qquad
B_N\le C\left(1+\sum_{k\le2N}k^{-2\psi}\right).                   \tag{13.6}
\]

若 \(\psi>1/2\)，则 \(B_N=O(1)\)、\(A_N=o(\sqrt N)\)。由(13.5)，\(N^{-1/2}\sum fP(Y)\) 的 r≥3阶累积量趋于0。若 \(\psi=1/2\)，则 \(A_N=O(\sqrt N)\)、\(B_N=O(\log N)\)，故 \((N\log N)^{-1/2}\sum fP(Y)\) 的 r≥3阶累积量为

\[
O((\log N)^{1-r/2})\longrightarrow0.                             \tag{13.7}
\]

只要相应二阶矩有极限，矩与累积量公式即给有限多项式 CLT。合法性同文件11：高阶偶数矩有界保证子列极限继承全部矩，Gaussian矩序列通过 \(E\cosh(aU)=e^{a^2v/2}\) 给出指数可积性，从而唯一决定分布。

## 3. 短记忆方差与对数 CLT

固定滞后 k 时，文件12的(12.13)给 \(r_n(i,i+k)\to g_1(h,k)\)，在目标窗口内一致。实际权重满足

\[
\frac1N\sum_i f_{n,i}f_{n,i+k}\to\int\omega^2.                   \tag{13.8}
\]

按滞后分组的对数协方差和由 \(C(1+|k|)^{-2\psi}Eg(Z)^2\) 控制；\(2\psi>1\) 时可求和。因此主导收敛给出(13.2)中的方差极限。其正性来自 k=0 的正方差项、所有偶数Hermite项非负及 \(\int\omega^2>0\)。

固定 Hermite 截断 \(P_K\) 的 CLT 由第2节得到。余项 \(R_K=g-P_K\) 满足

\[
E\left|\frac1{\sqrt N}\sum_i f_{n,i}R_K(Y_i)\right|^2
 \le C\sum_{\ell>K}b_\ell^2\ell!\to0,
\]

一致于 n。先取 n极限，再令K趋于无穷，得到(13.2)。这也处理了对数在0附近的奇异性。

## 4. 临界方差：非恒定 H 的实际替换已经验证

现在 \(h=3/4\)、\(\psi=1/2\)、\(c=h(2h-1)=3/8\)。文件12的(12.12)推出，对 \(k=|i-j|\ge3\)，

\[
\left|r_n(i,j)^2-\frac{c^2}{k}\right|
 \le C(k^{-3}+\varepsilon_n k^{-1}),\qquad \varepsilon_n\to0.      \tag{13.9}
\]

平方时使用 \(|r_n(i,j)|\le C k^{-1/2}\)。因此，在 \(N\log N\) 归一化的带权双和中，该替换误差为 \(O(1/\log N+\varepsilon_n)\)。有限个小滞后也只贡献 \(O(1/\log N)\)。

记 \(F_n(k)=N^{-1}\sum_i f_{n,i}f_{n,i+k}\)。由 \(\omega\) 的全局 Lipschitz 性、紧支集及(13.1)，

\[
F_n(0)\to\int\omega^2,\qquad
|F_n(k)-F_n(0)|\le C\min(|k|/N,1)+C/N.
\]

故 \(\sum_{k=1}^{\lceil2N\rceil}(F_n(k)-F_n(0))/k=O(1)+O(\log N/N)\)。正负两个滞后方向给出

\[
\frac1{N\log N}\sum_{i,j}f_{n,i}f_{n,j}r_n(i,j)^2
 \longrightarrow 2c^2\int\omega^2.                              \tag{13.10}
\]

对数的二阶Hermite系数 \(b_2=1\)，而 \(EH_2(Y_i)H_2(Y_j)=2r_n(i,j)^2\)，所以极限方差是

\[
4c^2\int\omega^2=\frac9{16}\int\omega^2.
\]

对 \(P=H_2\)，第2节直接给临界 CLT。其余Hermite项从4阶开始，由 \(\sum_k(1+|k|)^{-2}<\infty\)，有

\[
E\left|\frac1{\sqrt{N\log N}}\sum_i f_{n,i}(g-H_2)(Y_i)\right|^2
 \le C/\log N\to0.
\]

得到(13.3)。这里 \(H(t_i)\) 可在3/4两侧变化；\(b\log n\to0\) 保证这种局部变化在(12.10)、(13.9)中得到一致控制。文件03所保留的非恒定H临界替换缺口，现已在一维 q=1 内部点补齐。

## 5. 反演负号与中心化

设 \(\mu_n=E\widehat G(t)\)、\(\theta_n=(c_\sigma-\mu_n)/(2L)\)。文件12证明 \(\theta_n\to h\)，且真实方差 \(V_n=O(a_n^{-2})\)。在截断不发生的事件上，有精确等式

\[
2a_nL(\widehat H-\theta_n)=-a_n(\widehat G-\mu_n).
\]

截断事件包含于 \(\{|\widehat G-\mu_n|\ge cL\}\)，概率至多 \(CV_n/L^2\to0\)。所以此等式的差趋于概率0。又由(12.15)，

\[
a_nL|E\widehat H-\theta_n|\le C a_nV_n/L=O((a_nL)^{-1})\to0.
\]

这证明(13.4)，并明确处理了真实期望中心。相同论证适用于文件14的非正态极限，但在那里必须保留负号。

## 6. 短记忆最优带宽的实际修正版3.5

若 p为整数且H在t处具有p阶 Peano Taylor 展开，令

\[
R_H(t)=\frac{H^{(p)}(t)}{p!}\int z^p\omega(z)\,dz.
\]

实际权重再现及文件12给出

\[
B_n:=E\widehat G-G_n(h)=-2Lb^pR_H(t)+o(Lb^p)+O(\rho_n(t)).
\]

在短记忆 \(h<3/4\) 下，取 \(b_0=(nL^2)^{-1/(2p+1)}\)、\(b/b_0\to c_0\in(0,\infty)\)、\(A_n=(n^p/L)^{1/(2p+1)}\)。有 \(A_nLb_0^p=1\)，且 \(A_n\rho_n(t)\to0\)，因为 \(\psi>1/2>p/(2p+1)\)。于是

\[
A_n(\widehat G-G_n(h))\Rightarrow N(-2c_0^pR_H(t),c_0^{-1}V_h),
\]

\[
2(nL^2)^{p/(2p+1)}(\widehat H-h)
 \Rightarrow N(2c_0^pR_H(t),c_0^{-1}V_h).                           \tag{13.11}
\]

均值修正不再只是抽象传递结论，q=1短记忆实际模型的输入也已补齐。R=0时仍按加法展开处理。

## 7. 对原文结论的影响

短记忆和临界的归一化、Gaussian极限类型可以保留。临界方差必须改成 \((9/16)\int\omega^2\)，而非核中心值平方；文件03给出的合法零中心值核反例现在有了实际非恒定H版本的完整替代理论。一般反演负号仍不可删除。长记忆实际极限和循环积分识别另见文件14；本文不认证高维或未知尺度结论。
