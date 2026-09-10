# 第十一阶段：实际一阶差分的均值与谱函数高阶正则性

新增29条数学定理，累计514条数学定理及3条编号检查。完整原编号结果仍为2/27。主线未完成。

## 实际q=1增量与均值

在固定0<a≤H≤b<1区间，谱特征F_h(t)的已有统一参数L²界给出

\[
U=\ell^{-h}(F_h(s+\ell)-F_h(s)),\quad
W=\ell^{-h}(F_k(s+\ell)-F_h(s)),\quad \|U\|=1,
\]
\[
\|W-U\|\le CB\ell^{1-b},\qquad |k-h|\le B\ell.
\]

有效范围为0<ell≤1及|s+ell|≤1，允许区间靠近或从原点开始。若右侧ε≤1/2，则

\[
\|W\|^2\ge1/4,\qquad |\|W\|^2-1|\le\varepsilon(2+\varepsilon),
\qquad |\log\|W\|^2|\le10\varepsilon.
\]

`varyingPair_uniform_log_mean`将它接到实际Gaussian对数积分；`harmonizableGaussian_difference_log_mean_bound`再接到任意有限联合观测分布中的两坐标差，不假设两点独立。

最后，`hurstHolder_grid_firstDifference_log_mean_eventually`使用第十阶段的原类统一Lipschitz界，证明：对p≥1、M≥0，存在只依赖p和固定值域的C≥0，充分大的n对所有类内H和有效i统一满足

\[
\left|E\log(X(t_{i+1})-X(t_i))^2-
\{-2H(t_i)\log n+E\log Z^2\}\right|
\le10C(1+M)n^{b-1}.
\]

这里使用实际单位尺度谐和Gaussian网格分布。共同非零尺度可以通过已证明的Gaussian尺度恒等式接入，但本阶段最终网格定理还未显式封装这一推广。该较粗但全域统一的均值界不替代原文所有更精细rho分支。

## 高阶谱正则性

`SpectralSmooth`证明全部对数加权谱积分均可逐次求导：

\[
J_k(h)=\int(\log|x|)^k f_{h,t}(x)\,dx,
\quad J_k'(h)=-2J_{k+1}(h).
\]

每次求导的共同可积控制由两个端点密度及已证明的对数权重积分提供。因此D、归一化因子1/(sqrt(2)D)在(0,1)无限可微；每个固定阶导数在紧Hurst区间上一致有界。协方差系数D((h+k)/2)^2/(2D(h)D(k))的全部Fréchet导数也在紧参数矩形上一致有界。

| 模块 | 定理数 |
|---|---:|
| VaryingIncrement | 11 |
| GridLogMean | 9 |
| SpectralSmooth | 9 |

## 尚未完成

q=2变化参数的高阶抵消、差分之间的相关衰减、Gaussian对数协方差与高阶矩、实际估计器风险、未知尺度与短/临界/长记忆极限。已有均值和偏差不能替代这些证明。
