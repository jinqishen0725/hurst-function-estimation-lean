# 14. 一阶差分长记忆：实际统计量、循环积分与非正态极限

对应：Theorem 3.3(iii)、Theorem 3.4 的长记忆分支，以及 S.3.2 的循环积分。在一维、q=1、已知尺度、固定内部点的范围内，补齐[文件08](08_centering_and_long_memory.md)此前保留的“实际统计量收敛”和“循环积分与谱识别”两项缺口。

**状态：下述普通数学证明闭合，尚未转 Lean。** 本证明允许 H 非恒定、局部多项式等价核有符号；不声称高维、未知尺度或全边界结论。

## 1. 模型、算子和结论

采用[文件12](12_q1_mbm_covariance_mse.md)的全部模型、内部光滑性和带宽条件，固定 \(t\)，现在设

\[
h=H(t)>3/4,\quad \psi=2-2h\in(0,1/2),\quad c=h(2h-1)>0,
\quad N=nb,\quad L=\log n.
\]

\(\omega\) 为实际局部多项式设计的等价核，\(\int\omega=1\)。在 \(E=L^2([-1,1])\) 上定义实对称积分算子

\[
(\mathcal K f)(x)=c\int_{-1}^1|x-y|^{-\psi}f(y)\,dy.
\]

其核平方可积，因为 \(2\psi<1\)，所以 \(\mathcal K\) 是 Hilbert–Schmidt 紧算子。第2节将从实际相关矩阵证明它非负。令 \(M_\omega\) 为乘以 \(\omega\) 的有界自伴算子，并定义

\[
\mathcal A=\mathcal K^{1/2}M_\omega\mathcal K^{1/2}.                \tag{14.1}
\]

第4节证明 \(\mathcal A\) 是自伴 Hilbert–Schmidt 算子，即使 \(\omega\) 有符号也成立。记其含重数的非零特征值为 \(\lambda_j\in\mathbb R\)，\(\sum_j\lambda_j^2<\infty\)。用独立标准正态 \(Z_j\) 定义

\[
Q=\sum_j\lambda_j(Z_j^2-1),                                      \tag{14.2}
\]

按 \(L^2\) 收敛。我们证明

\[
N^\psi(\widehat G(t)-E\widehat G(t))\Rightarrow Q,                 \tag{14.3}
\]

\[
2N^\psi L(\widehat H(t)-E\widehat H(t))\Rightarrow -Q.             \tag{14.4}
\]

Q非退化且非Gaussian。其全实轴特征函数为

\[
\varphi_Q(u)=\exp\sum_j\left[-iu\lambda_j
                       -\tfrac12\operatorname{Log}(1-2iu\lambda_j)\right].
                                                                    \tag{14.5}
\]

只有在 \(2|u|\sup_j|\lambda_j|<1\) 时，才可使用原文形式的 Taylor 级数。

## 2. 实际相关矩阵的积分算子极限

令 \(z_i=(t_i-t)/b\)，步长为 \(1/N\)。取所有 \(|z_i|\le1+1/N\) 的下标组成 \(\Lambda_n\)，并令

\[
I_{n,i}=[z_i-1/(2N),z_i+1/(2N)).
\]

这些完整小区间不交，最终位于固定 \([-2,2]\)，其并集趋近 \([-1,1]\)。稍宽窗口不改变文件12的估计；宽度仍为 \(O(b)\)，固定滞后和冻结误差常数相同量级。

在 \(L^2([-2,2])\) 上定义阶梯核

\[
K_n(x,y)=N^\psi r_n(i,j),\quad x\in I_{n,i},y\in I_{n,j},
\]

在小区间并集外补零。正交基 \(e_i=\sqrt N\mathbf1_{I_{n,i}}\) 下，其非零矩阵为
\(N^{\psi-1}R_n\)，其中 \(R_n=(r_n(i,j))\) 是**真实** Gaussian 相关矩阵。因此每个 \(\mathcal K_n\) 自伴非负。

把极限核扩展为

\[
K(x,y)=c\,\mathbf1_{[-1,1]}(x)\mathbf1_{[-1,1]}(y)|x-y|^{-\psi}.
\]

证明

\[
\|K_n-K\|_{L^2([-2,2]^2)}\to0.                                   \tag{14.6}
\]

离开对角线 \(|x-y|\ge\varepsilon>0\) 时，\(|i-j|/N\to|x-y|\)。文件12的增长滞后估计(12.12)给出 \(K_n(x,y)\to K(x,y)\)，除支集边界外成立，并在这个区域有统一界。于是主导收敛处理离对角线部分。

靠近对角线则用真实相关界：

\[
\iint_{|x-y|\le\varepsilon}|K_n(x,y)|^2dxdy
 \le C N^{2\psi-1}\left(1+\sum_{k\le\varepsilon N+2}k^{-2\psi}\right)
 \le C\{N^{2\psi-1}+\varepsilon^{1-2\psi}\}.                      \tag{14.7}
\]

极限核有同样的 \(C\varepsilon^{1-2\psi}\) 界。先令n趋于无穷，再令ε趋于0，得到(14.6)。这同时处理了对角单元，不把相关系数在k=0处的1替换成一个无穷大值。

Hilbert–Schmidt 收敛蕴含算子范数收敛，所以对任意f，\(\langle f,\mathcal K f\rangle=\lim_n\langle f,\mathcal K_nf\rangle\ge0\)。限制到 \([-1,1]\) 即得到第1节所用的非负算子。

## 3. 循环乘积的真实极限

定义阶梯权重 \(f_n(x)=Nw_i(t)\) 于 \(I_{n,i}\)，其他地方为0。所有非零权重被 \(\Lambda_n\) 包含。由文件02的离散权重展开及 \(\omega\) 的 Lipschitz 性，

\[
\|f_n-\omega\|_\infty\to0,
\]

其中 \(\omega\) 在 \([-1,1]\) 外补零。令 \(\mathcal T_n=M_{f_n}\mathcal K_n\)、\(\mathcal T=M_\omega\mathcal K\)，则

\[
\|\mathcal T_n-\mathcal T\|_{\rm HS}\to0,
\qquad \operatorname{tr}(\mathcal T_n^r)\to\operatorname{tr}(\mathcal T^r),
\quad r\ge2.                                                     \tag{14.8}
\]

第二条由乘积差的逐项展开推出：至少两个因子以HS范数控制，剩余因子以一致算子范数控制，使用 \(|\operatorname{tr}(AB)|\le\|A\|_{\rm HS}\|B^*\|_{\rm HS}\)。

有限矩阵的迹明确为

\[
\operatorname{tr}(\mathcal T_n^r)
 =N^{r(\psi-1)}\sum_{i_1,\ldots,i_r}
 \prod_{a=1}^r f_{n,i_a}r_n(i_a,i_{a+1}),\quad i_{r+1}=i_1.
\]

极限迹等于原文需要的循环积分修正版

\[
S_r=c^r\int_{[-1,1]^r}
 \prod_{a=1}^r\omega(x_a)|x_a-x_{a+1}|^{-\psi}
 \,dx_1\cdots dx_r,\quad x_{r+1}=x_1.                            \tag{14.9}
\]

这些积分**绝对收敛**。一种不依赖未证明循环积分估计的验证如下：把非负对称核 K 截成 \(K^{(M)}=\min(K,M)\)，其HS范数不超过K，且 \(\|\mathcal K^{(M)}\|_{\rm op}\le\|\mathcal K\|_{\rm op}\)，因为 \(|\mathcal K^{(M)}f|\le\mathcal K|f|\)。有界核的循环积分经Fubini等于相应幂的迹，绝对值不超过 \(\|\mathcal K\|_{\rm op}^{r-2}\|\mathcal K\|_{\rm HS}^2\)。无权的非负循环积分可用单调收敛令M趋于无穷；再乘 \(\|\omega\|_\infty^r\) 即控制带权积分的绝对值。最后HS收敛、迹连续性和主导收敛共同给出(14.9)。

因此实际离散循环乘积已经收敛到 S_r，而非把这一步当作外部输入。

## 4. 自伴二次型与谱的识别

\(\mathcal K\) 有非负特征值 \(\kappa_j\)，\(\sum\kappa_j^2<\infty\)。在其特征基中，\(\mathcal A\) 的矩阵元为
\(\sqrt{\kappa_i\kappa_j}\langle e_i,M_\omega e_j\rangle\)。因此

\[
\begin{aligned}
\|\mathcal A\|_{\rm HS}^2
&=\sum_{i,j}\kappa_i\kappa_j|\langle e_i,M_\omega e_j\rangle|^2\\
&\le\frac12\sum_{i,j}(\kappa_i^2+\kappa_j^2)
              |\langle e_i,M_\omega e_j\rangle|^2
\le\|\omega\|_\infty^2\sum_i\kappa_i^2<\infty.
\end{aligned}                                                       \tag{14.10}
\]

若有零特征子空间，相应项为0。对K作有限谱截断，所得A的双下标截断在HS范数中趋于A。有限维迹的循环恒等式，再取HS极限，给出

\[
\operatorname{tr}(\mathcal A^r)
 =\operatorname{tr}((M_\omega\mathcal K)^r)=S_r
 =\sum_j\lambda_j^r,\qquad r\ge2.                                \tag{14.11}
\]

这补齐循环积分与真正自伴二阶Gaussian混沌的谱识别；无需假设权重非负，也没有假设 \(\mathcal K\) 是迹类算子。

## 5. 实际二阶项的分布收敛

考虑实际统计量的二阶Hermite部分

\[
Q_n=N^{\psi-1}\sum_i f_{n,i}(Y_i^2-1).
\]

有限Gaussian向量可写成 \(Y=R_n^{1/2}Z\)。因此Q_n是中心化二次型，其实对称矩阵为

\[
A_n=N^{\psi-1}R_n^{1/2}\operatorname{diag}(f_{n,i})R_n^{1/2}.
\]

其特征值记作 \(\lambda_{n,j}\)。有限循环迹恒等式与(14.8)给出

\[
\operatorname{tr}(A_n^r)=\operatorname{tr}(\mathcal T_n^r)
 \longrightarrow S_r=\operatorname{tr}(\mathcal A^r),\quad r\ge2.
                                                                    \tag{14.12}
\]

同时 \(\|A_n\|_{\rm op}\le\|f_n\|_\infty\|\mathcal K_n\|_{\rm op}\le C\)，且
\(\sum_j\lambda_{n,j}^2=\operatorname{tr}(A_n^2)\le\|\mathcal T_n\|_{\rm HS}^2\le C\)。

有限中心化Gaussian二次型的累积量（由独立 \(Z_j^2-1\) 的生成函数直接展开）是

\[
\kappa_r(Q_n)=2^{r-1}(r-1)!\operatorname{tr}(A_n^r),\quad r\ge2.
\]

由(14.12)，全部矩趋于Q的对应矩。为避免只凭矩收敛作结论，取固定足够小 \(a>0\)，满足 \(2a\sup_n\|A_n\|_{\rm op}<1\)。中心化卡方的有限乘积公式和
\(\sum_j|\lambda_{n,j}|^r\le C^{r-2}\sum_j\lambda_{n,j}^2\) 给出

\[
\sup_n E e^{a|Q_n|}<\infty.
\]

Q亦有同样的局部指数矩，见文件08或对其有限部分用同一界和Fatou。于是二阶矩保证紧性，指数矩保证各阶矩的一致可积性；任何子列极限继承Q的矩。存在局部指数矩的分布由其矩唯一决定（特征函数在复平面的一个带状邻域解析，其零点附近Taylor系数由矩给出）。所以

\[
Q_n\Rightarrow Q.                                                \tag{14.13}
\]

这里不需要未经证明的“非自伴矩阵逐个特征值收敛”，也不需要假设平方根算子的HS连续性。

## 6. 所有高阶Hermite项都消失

\(g-H_2\) 的Hermite最低阶为4。文件12的真实相关衰减给出

\[
\begin{aligned}
E\left|N^{\psi-1}\sum_i f_{n,i}(g-H_2)(Y_i)\right|^2
&\le C N^{2\psi-1}\left(1+\sum_{k\le2N}k^{-4\psi}\right)
\longrightarrow0.
\end{aligned}                                                       \tag{14.14}
\]

分别验证：4ψ>1时为 \(O(N^{2\psi-1})\)；4ψ=1时为 \(O(N^{-1/2}\log N)\)；4ψ<1时为 \(O(N^{2\psi-1}+N^{-2\psi})\)。因 \(0<\psi<1/2\)，均趋于0。Hermite系数的平方和有限使此界适用于整个无限尾项。

(14.13)–(14.14)即证明(14.3)，不再以Taqqu型极限定理作为尚待匹配条件的黑箱。

## 7. 非退化、非Gaussian及反演符号的实际影响

首先

\[
\operatorname{Var}Q=2S_2
=2c^2\iint\omega(x)\omega(y)|x-y|^{-2\psi}\,dxdy>0.               \tag{14.15}
\]

即使ω有符号，严格正性也成立。令 \(\beta=2\psi\in(0,1)\)，用正核分解

\[
|x-y|^{-\beta}=\frac1{\Gamma(\beta)}\int_0^\infty a^{\beta-1}e^{-a|x-y|}\,da,
\]

以及

\[
e^{-a|x-y|}=2a\int_{-\infty}^{\min(x,y)}e^{-a(x-u)}e^{-a(y-u)}\,du.
\]

带ω的二次积分因此是非负平方的积分。对每个a>0，若该平方积分为0，则
\(F(u)=\int_u^\infty\omega(x)e^{-a(x-u)}dx\) 恒为0；由 \(F'=aF-\omega\) 得ω=0，矛盾于 \(\int\omega=1\)。所有交换的绝对可积性由β<1及ω有界紧支撑保证。故(14.15)严格为正。

又因A非零，Q的第四累积量 \(48\sum_j\lambda_j^4>0\)，所以Q不可能是Gaussian。

文件13第5节的精确仿射反演论证取 \(a_n=N^\psi\) 仍成立，文件12又给 \(V_n=O(N^{-2\psi})\)。所以得到(14.4)，包括从确定性中心换成真实期望中心。

**原文漏负号确会在合法实例中改变极限分布。** 取p=2、非负对称非零核K，则局部线性等价核 \(\omega=K/\int K\ge0\)。取任何满足本文件条件且 \(H(t)>3/4\) 的H，例如常数H。此时A非负且非零，故

\[
EQ^3=8\operatorname{tr}(\mathcal A^3)>0,
\qquad E(-Q)^3<0.
\]

因此Q与−Q不同分布。这是在原模型允许的子模型中、实际统计量极限上的区别，不只是一个抽象二次型例子。

## 8. 特征函数及原循环积分公式应如何修改

文件08已证明平方可和特征值给出全实轴公式(14.5)。结合现在证明的(14.11)，仅在
\(2|u|\sup_j|\lambda_j|<1\) 内可写

\[
\log\varphi_Q(u)=\frac12\sum_{r=2}^\infty\frac{(2iu)^r}{r}S_r.
\]

S_r恰为(14.9)。系数使用 \(c=h(2h-1)\)，即原文导数定义中的正确1/2；不能使用主文一维显式乘积中漏1/2的数值。H估计量则用 \(\varphi_Q(-u)\)。

**影响判断：** 一维q=1长记忆的归一化 \((nb)^\psi\) 和非Gaussian二阶混沌类型保留。必须修正一维系数、全实轴特征函数写法，以及反演后整个极限分布的反射。现在这些修改都已对应到实际mBm统计量；仍不意味着高维或未知尺度结果完成。

## 附：有限计算核对

[数值记录](../verification/q1_mbm_checks.json)包含n=128、256、512、1024，目标H=0.62、0.75、0.82，常H及斜率0.06的线性H，共24种实际中点网格模型。真实协方差差分与常H冻结公式最大误差约1.8×10^−11；实际Gaussian二次型的谱幂和与循环迹最大差约9×10^−15。记录也保留有限样本的方差尺度与算子距离，未把它们当成极限证明。
