# 12. 一维一阶差分：真实协方差、三种方差率与 MSE

**后续进展：** [文件18](18_full_domain_l2_minimax.md)已补齐所列一维短记忆分支的全域MSE及同一函数类上1≤s≤2的minimax匹配；本文件的内部证明或原先缺口记录不包含这项后续边界论证。p=1下界、s>2匹配上界和高维仍待证。

对应：Theorem 8.2、Lemma 8.3、Theorem 3.2、Theorem 3.4 的 d=1、q=1 分支；S.2.3、S.3.1、S.3.3。本文件处理实际非恒定 H，后续概率极限见文件13/14。

**状态：以下明确范围内的普通数学证明闭合，尚未转 Lean。** 已知尺度、固定内部区间、单位差分方向；不声称全边界或高维结论。

## 1. 假设与主要结论

沿用[文件10](10_q2_mbm_mse.md)的实际一维 mBm、协方差 C（已除以尺度平方）、中点网格、内部区间 I、稍大的工作区间 J 和核条件。现在取 q=1、p≥1，H在稍大内部区间上 Lipschitz，且具有有界 \(C^{m,\alpha}\) 范数，\(m=\lceil p\rceil-1\)、\(\alpha=p-m\in(0,1]\)。H值在固定 \([\eta,1-\eta]\) 内。论文 Hölder 类配合值域界可给出所需内部范数，论证同文件10第9节（p=1时用一阶导数振幅与均值定理）。

令 \(L=\log n\)、\(N=nb\)，要求

\[
b\to0,\quad N\to\infty,\quad bL\to0.                             \tag{12.1}
\]

原文带宽条件蕴含这些要求。定义

\[
D_i=X(t_i+1/n)-X(t_i),\quad W_i=\sigma^{-1}n^{H(t_i)}D_i,
\quad Y_i=D_i/\sqrt{\operatorname{Var}D_i},
\quad \widehat G(t)=\sum_iw_i(t)\log D_i^2.
\]

使用有效基点 \(i\le n-1\)。局部多项式权重完全沿用文件02；所有非零权重对应的差分点最终都在工作区间内。q=1时

\[
G_n(h)=c_\sigma-2Lh,\qquad c_\sigma=\log\sigma^2+\mu_0,
\quad \mu_0=E\log Z^2,
\quad \widehat H(t)=\operatorname{clip}_{[0,1]}
 \frac{c_\sigma-\widehat G(t)}{2L}.
\]

对固定 \(t\in I\)，写

\[
h=H(t),\qquad \psi=2-2h\in(0,2),\qquad
\rho_n(t)=L/n+n^{-\psi}.
\]

本文件证明

\[
|E\widehat G(t)-G_n(h)|\le C(Lb^p+\rho_n(t)),                     \tag{12.2}
\]

\[
\operatorname{Var}\widehat G(t)\le C T_\psi(N),\qquad
T_\psi(N)=
\begin{cases}
N^{-1},&\psi>1/2,\\
N^{-1}\log N,&\psi=1/2,\\
N^{-2\psi},&0<\psi<1/2,
\end{cases}                                                       \tag{12.3}
\]

\[
E|\widehat H(t)-h|^2\le C\left(b^{2p}+\frac{\rho_n(t)^2}{L^2}
                       +\frac{T_\psi(N)}{L^2}\right).             \tag{12.4}
\]

三分支常数不声称跨 \(\psi=1/2\) 一致；需要跨临界一致性时使用第5节未拆分的幂和。固定阈值间隔以及统一内部范数下，相应界可对 t 一致。

## 2. 协方差混合导数：补回光滑背景

真实协方差为

\[
C(s,u)=B(H(s),H(u))\{s^a+u^a-|s-u|^a\},\quad a=H(s)+H(u),
\quad B(h,h)=1/2.
\]

B光滑且所需参数导数有界。先对光滑H证明，再以保持 Lipschitz 界的平滑卷积取极限。每个变量只微分一次，以下界只用 H 的一阶导数界。

记 \(r=|s-u|>0\)。光滑背景 \(B(s^a+u^a)\) 的混合导数为 \(O(1)\)。奇异部分的混合导数主项为

\[
B(H(s),H(u))a(a-1)r^{a-2}.
\]

其余项是有界系数乘 \(r^{a-j}(\log r)^k\)，\(j+k\le2\)、\(j<2\)，相对主幂不超过 \(Cr(1+|\log r|)\)。冻结H并使用 \(|H(u)-H(s)|\le Cr\)，得

\[
|\partial_s\partial_u C(s,u)|\le C r^{H(s)+H(u)-2},                \tag{12.5}
\]

\[
\partial_s\partial_u C(s,u)
=\{c_1(H(s))+O(r(1+|\log r|)+r^{\psi(s)})\}r^{-\psi(s)},
\quad c_1(h)=h(2h-1),\quad \psi(s)=2-2H(s).                       \tag{12.6}
\]

其中 \(r^{\psi(s)}\) 来自 O(1) 光滑背景。**若 \(H(s)>1/2\)，则 \(\psi(s)<1\)，不能把它一般地吸入 \(O(r|\log r|)\)。** 这里修正的是原导数余项，不能预先忽略该项。对于 Lipschitz H，有限差分结论由平滑逼近成立；导数式可按几乎处处意义理解。

### 2.1 原S.2.3的余项确有反例，不只是证明省略

取 \(h_0=3/4\)、\(t_0=e^{-1/(4h_0)}=e^{-1/3}\)，以及

\[
H_\varepsilon(x)=h_0+\varepsilon(x-t_0),\qquad \varepsilon>0\text{ 足够小}.
\]

这是合法、光滑、远离0和1的Hurst函数。令光滑背景为
\(P(s,u)=B(H_\varepsilon(s),H_\varepsilon(u))(s^a+u^a)\)。B对称且 \(B(h,h)=1/2\)，所以 \(B_h(h,h)=B_k(h,h)=0\)。直接求导得到

\[
\partial_s\partial_uP(t_0,t_0)
=\varepsilon t_0^{2h_0-1}(2h_0\log t_0+1)
 +\varepsilon^2t_0^{2h_0}\{2B_{hk}(h_0,h_0)+(\log t_0)^2\}
=\tfrac12\varepsilon t_0^{2h_0-1}+O(\varepsilon^2)>0.              \tag{12.6a}
\]

固定这样一个小ε。第2节对奇异项单独计算的余项是
\(O(r^{1-\psi_0}(1+|\log r|))=o(1)\)，\(\psi_0=1/2\)。因此

\[
\lim_{r\downarrow0}
\{\partial_s\partial_uC(t_0,t_0+r)-c_1(h_0)r^{-\psi_0}\}
=\partial_s\partial_uP(t_0,t_0)>0.                                \tag{12.6b}
\]

而原S.2.3的相对 \(O(r\log r)\) 余项会令上述差趋于0，矛盾。故它的主项展开按原文书写确实不成立。补上相对 \(O(r^\psi)\) 后，(12.6)成立；本文件及文件13/14证明该修正不改变所列一维方差率与极限类型。

## 3. 实际有限差分协方差

记 \(C_n(s,u)=E[W_n(s)W_n(u)]\)。冻结函数为

\[
g_1(h,k)=\tfrac12\{|k+1|^{2h}+|k-1|^{2h}-2|k|^{2h}\},
\quad g_1(h,0)=1.
\]

### 3.1 有界滞后与正方差

对固定 M、\(|k|\le M\)，将实际协方差四个奇异项分别写为 n 的幂乘 \(|k+j-i|\) 的幂。H端点变化是 \(O_M(1/n)\)，n的幂变化带来 \(O_M(L/n)\) 误差；距离幂对指数的导数在有界距离和正指数紧区间上有界，包括其在0处的连续延拓。光滑背景的二重差分为 \(O(n^{-2})\)，乘以归一化因子后为 \(O_M(n^{2H(s)-2})\)。故

\[
C_n(s,s+k/n)=g_1(H(s),k)
           +O_M(L/n+n^{-\psi(s)}).                               \tag{12.7}
\]

尤其

\[
\operatorname{Var}W_n(s)=1+O(L/n+n^{-\psi(s)}).                    \tag{12.8}
\]

H远离1保证误差一致趋于0，所以真实方差最终有一致正下界。对目标窗口 \(|s-t|\le b\)，\(n^{-\psi(s)}\le e^{CbL}n^{-\psi(t)}\)，从而窗口中的误差一致为 \(O(\rho_n(t))\)。

### 3.2 所有滞后

当 \(k=n|s-u|\ge2\)，二重差分等于

\[
\int_{[0,1/n]^2}\partial_x\partial_y C(s+v,u+w)\,dv\,dw.
\]

积分中距离与 \(k/n\) 可比，H的移位变化为 \(O(1/n)\)。由(12.5)，

\[
|C_n(s,u)|\le C k^{H(s)+H(u)-2}.                                 \tag{12.9}
\]

小滞后由(12.8)和 Cauchy–Schwarz 处理。对于同一目标窗口中的 i,j，用(12.1)冻结到目标点 h，并除以真实标准差，得到

\[
|r_n(i,j)|:=|E[Y_iY_j]|\le C(1+|i-j|)^{-\psi(t)}.                 \tag{12.10}
\]

这是实际非平稳相关界；局部窗口外不套用目标点指数。全工作区间上可保留(12.9)的双端点指数，或取 \(2-2\sup_JH\) 得较弱全局界。

### 3.3 增长滞后的修正版

设 \(2<|k|\le2nb\)。由(12.6)的积分表示、\(H(s+v)-H(s)=O(1/n)\)，以及归一化中的因子 \(n^{H(u)-H(s)}\)，有

\[
C_n(s,s+k/n)
 =\left\{c_1(H(s))+O\left(k^{-2}+\frac{|k|L}{n}
                  +( |k|/n)^{\psi(s)}\right)\right\}|k|^{-\psi(s)}.
                                                                    \tag{12.11}
\]

具体而言，\(n^{H(u)-H(s)}=1+O(|k|L/n)\)；移位H导致的幂误差为 \(O(L/n)\)；导数的距离对数余项至多 \(C|k|L/n\)；光滑背景给最后一项。剩下的冻结积分以 \(V=n(w-v)\) 表示，\(EV=0,|V|\le1\)，二阶 Taylor 公式给

\[
E|k+V|^{-\psi(s)}=|k|^{-\psi(s)}(1+O(k^{-2})).
\]

所有余项是绝对系数误差，不除以可能为0的 c₁。这补足8.2(iv)所需的真实非恒定H版本；原仅有 \(O(b\log b)\) 的余项不能保留。

### 3.4 供极限证明使用的统一形式

固定 t，令 \(c=h(2h-1)\)。对窗口中所有 \(k=|i-j|\ge3\)，由(12.8)、(12.11)、\(|H(t_i)-h|\le Cb\)，

\[
|r_n(i,j)-c k^{-\psi}|\le C\{k^{-\psi-2}+\varepsilon_n k^{-\psi}\},
\quad \varepsilon_n=bL+b^\psi+\rho_n(t)\to0.                      \tag{12.12}
\]

例如 \((k/n)^{\psi(t_i)}\le Cb^\psi\)，额外因子由 \(e^{Cb|\log b|}\) 控制；\(k^{\psi-\psi(t_i)}=1+O(bL)\)。对任意固定整数 k，另有

\[
\sup_{i:\ |t_i-t|\le b}|r_n(i,i+k)-g_1(h,k)|\to0.                \tag{12.13}
\]

这两条分别控制增长滞后和固定滞后，后续无需再假设平稳替换成立。

## 4. 对数均值与实际平滑偏差

Gaussian 缩放给出精确关系

\[
E\log D_i^2=c_\sigma-2LH(t_i)+\log\operatorname{Var}W_i.
\]

由(12.8)，目标窗口中的最后一项为 \(O(\rho_n(t))\)。文件02的真实网格权重满足精确多项式再现、\(\sum|w_i|\le C\)、\(\max|w_i|\le C/N\)。因此

\[
E\widehat G(t)-G_n(h)
=-2L\left(\sum_iw_iH(t_i)-H(t)\right)+O(\rho_n(t)),
\]

直接得到(12.2)，无需引入偏差的数值求积项。

## 5. 三种方差率与跨临界界

令 \(g(z)=\log z^2-\mu_0\)。Gaussian Hermite 恒等式给

\[
|\operatorname{Cov}(g(Y_i),g(Y_j))|\le Eg(Z)^2\,r_n(i,j)^2.
\]

故实际方差满足未拆分的界

\[
\operatorname{Var}\widehat G(t)
 \le \frac C N\left(1+\sum_{k=1}^{\lceil2N\rceil}k^{-2\psi}\right).
                                                                    \tag{12.14}
\]

积分比较推出(12.3)。若希望常数跨临界一致，可将括号估为 \(C(1+J_{1-2\psi}(2N))\)，其中

\[
J_a(R)=\begin{cases}(R^a-1)/a,&a\ne0,\\ \log R,&a=0.\end{cases}
\]

在H的固定紧区间内比较常数一致。不能把三个分支分别产生的、随 \(|1-2\psi|^{-1}\) 增大的常数误称为跨临界一致。

## 6. MSE、精细偏差与速率

双端截断不会增加相对于 h 的误差，故

\[
|\widehat H(t)-h|\le |\widehat G(t)-G_n(h)|/(2L).
\]

平方取期望得到(12.4)。还可得到精细偏差：记 \(B_n=E\widehat G-G_n(h)=o(L)\)、\(V_n=\operatorname{Var}\widehat G\)，并设 \(\theta_n=(c_\sigma-E\widehat G)/(2L)\)。它最终在固定内部H区间。未截断的逆是精确仿射，截断只可能发生于 \(|\widehat G-E\widehat G|\ge cL\)。由二阶矩控制该尾部，得到

\[
|E\widehat H-\theta_n|\le C V_n/L^2,\qquad
E\widehat H-h=-B_n/(2L)+O(V_n/L^2).                               \tag{12.15}
\]

具体地，截断造成的差至多 \(|\widehat G-E\widehat G|/(2L)\) 乘上述尾事件的指标，期望至多 \(CV_n/L^2\)。

由(12.4)还得到以下点态带宽与平方风险上界；临界处 \(\log N\asymp L\)：

| 记忆范围 | 带宽量级 | 平方风险上界量级 |
|---|---|---|
| \(h<3/4\) | \((nL^2)^{-1/(2p+1)}\) | \((nL^2)^{-2p/(2p+1)}\) |
| \(h=3/4\) | \((nL)^{-1/(2p+1)}\) | \((nL)^{-2p/(2p+1)}\) |
| \(h>3/4\)，\(\psi=2-2h\) | \((n^\psi L)^{-1/(p+\psi)}\) | \((n^\psi L)^{-2p/(p+\psi)}\) |

这些带宽均满足(12.1)。在各自带宽下，\(\rho_n^2/L^2\) 为更低阶：短记忆用 \(\psi>1/2>p/(2p+1)\)，临界用 \(1/2>p/(2p+1)\)，长记忆用 \(\psi>\psi p/(p+\psi)\)。这里长记忆带宽依赖未知 h，是速率分析中的理论选择，不是已证明可实施的自适应选带宽方法；这些是该估计量的点态上界，不是三个新的minimax下界。

**影响判断：** 原导数和协方差余项需修改，但三种方差阶及由其推出的上述MSE上界可以保留。所有结论均已连接到真实mBm模型。概率极限仍须另证，见文件13/14。
