# 16. 未知尺度：真实空间平均、S.5.1反例与4.2修复

对应：Theorem 4.2、Lemma S.5.1、Lemma S.5.2。范围为文件15的一维q∈{1,2}实际模型，目标和平均中心位于固定内部区间I，工作区间J略大。q=1要求p≥1，q=2要求p≥2，H及所需内部范数一致受控。

**状态：以下普通数学证明闭合，尚未转Lean。** 本文件不把不同位置的pilot当作独立变量。原S.5.1的远距离项确有遗漏；第6节给出实际长记忆反例。不过修正后的界仍足以保留Theorem 4.2在本范围的主要MSE上界。

## 1. 定义和将要证明的界

置 \(L=\log n\)、\(b=b_1\)、\(N=nb\)，\(b\to0,N\to\infty\)。为得到原定理的简化率，采用论文带宽条件

\[
b(\log n)^k\to0\quad\text{对每个固定 }k>0.                      \tag{16.1}
\]

后面的未简化界只需文件15的bL→0。令

\[
\bar h=\sup_JH,\quad\bar\psi=2q-2\bar h,\quad
\bar\rho_n=\begin{cases}L/n+n^{-\bar\psi},&q=1,\\L/n,&q=2,\end{cases}
\quad a_n=b^p+\bar\rho_n,\quad B_n=La_n.
\]

平均中心取粗中点网格落在I中的点 \(s_j\)，间隔1/m，\(m\asymp b^{-1}\)，其个数记为M，故 \(M\asymp m\)。令P为文件15的pilot，\(P^\gamma=\operatorname{clip}_{[0,1-\gamma/2]}P\)，选固定 \(0<\gamma\le\eta\)，真实H属于 \([\eta,1-\eta]\)。定义 \(\ell(h)=\log v_q(h)\) 及原三步方法中的尺度估计

\[
\widehat s=\frac1M\sum_{j=1}^M
 \{G_1^{\wedge}(s_j)+2LP(s_j)-\ell(P^\gamma(s_j))-\mu_0\},
\qquad s=\log\sigma^2.                                          \tag{16.2}
\]

此处G₁也用带宽b₁。线性项2LP不截断；仅log v的输入按原构造截断。

记 \(T_\psi(x)\) 为文件12的三种方差函数。先证明未简化界

\[
E(\widehat s-s)^2
 \le C\{B_n^2+L^2T_{\bar\psi}(n)+T_{\bar\psi}(N)\},             \tag{16.3}
\]

\[
|E\widehat s-s|\le C\{B_n+T_{\bar\psi}(N)\}.                     \tag{16.4}
\]

在(16.1)下，\(L^2T_{\bar\psi}(n)=o(T_{\bar\psi}(N))\)，所以

\[
E(\widehat s-s)^2\le C\{B_n^2+T_{\bar\psi}(N)\}.                 \tag{16.5}
\]

若 \(T_{\bar\psi}(N)=O(B_n)\)，则偏差为O(Bₙ)。Bₙ比原T₁′少了不必要的平滑求积项，因此这些界足以推出原4.2对应范围的上界。

## 2. S.5.1的修复：合并实际权重

由两尺度的定义，尺度误差分解为 \(\widehat s-s=I_1+I_2\)，其中

\[
I_1=\frac1M\sum_j\{G_1^{\wedge}(s_j)-G_n(H(s_j))
                         +2L(P(s_j)-H(s_j))\},
\]

\[
I_2=-\frac1M\sum_j\{\ell(P^\gamma(s_j))-\ell(H(s_j))\}.
\]

这里 \(G_n(h)=s+\mu_0-2Lh+\ell(h)\)。先看I₁。文件15与局部平滑偏差立即给
\(|EI_1|\le CB_n\)。

定义合并权重

\[
\nu_{n,i}=\frac1M\sum_jw_i(s_j).
\]

它们满足

\[
\sum_i|\nu_{n,i}|\le C,\qquad
\max_i|\nu_{n,i}|\le\frac Cn.                                   \tag{16.6}
\]

第一条直接来自各局部权重的绝对和界。第二条的依据是：固定观测点tᵢ只落入 \(O(mb+1)\) 个粗网格窗口，每个非零局部权重不超过C/(nb)。故

\[
|\nu_{n,i}|\le C\frac{mb+1}{mnb}\le C/n
\]

，因为mb有固定正下界。此论证适用于有符号的高阶局部多项式权重，也明确说明“平均收益”来自覆盖次数，而非假设独立。

令 \(g_{i,a}=\log D_{i,a}^2-E\log D_{i,a}^2=g(Y_{i,a})\)。有精确恒等式

\[
I_1-EI_1=\sum_i\nu_{n,i}
 \left\{\left(1-\frac L{\log2}\right)g_{i,1}
                    +\frac L{\log2}g_{i,2}\right\}.              \tag{16.7}
\]

系数是L/log 2，来自2L乘pilot的1/(2log 2)。不能把它写成L/(2log 2)。

文件15的全工作区间交叉相关界及Hermite恒等式给所有a,b组合

\[
|\operatorname{Cov}(g_{i,a},g_{k,b})|
 \le C(1+|i-k|)^{-2\bar\psi}.
\]

由(16.6)，

\[
\operatorname{Var}I_1
 \le\frac{CL^2}{n}\left(1+\sum_{k\le Cn}k^{-2\bar\psi}\right)
 \le CL^2T_{\bar\psi}(n).                                       \tag{16.8}
\]

这是真实空间平均方差，不是把单点pilot的方差简单除以M。

## 3. 任意m时的近距离/远距离修正版

为准确对应S.5.1，若不预设mb有正下界，可使用以下一般估计，M≈m且m→∞：

\[
\operatorname{Var}I_1\le CL^2\left\{
 (b+m^{-1})T_{\bar\psi}(N)
 +m^{2\bar\psi-1}n^{-2\bar\psi}
  \sum_{\substack{1\le k\le m\\ k>3mb}}k^{-2\bar\psi}\right\}.    \tag{16.9}
\]

证明：两个中心相距不超过3b时，用Cauchy–Schwarz和单点方差界，其协方差不超过CT(N)。每个中心有O(mb+1)个这样的邻点，除以M²给第一项。相距k/m>3b时，两个窗口内任意观测点相距至少常数倍k/m；相关幂界和各权重绝对和界给协方差 \(C(nk/m)^{-2\bar\psi}\)。**每个滞后k有O(m)对中心**，故除以M²后为 \(m^{2\bar\psi-1}n^{-2\bar\psi}\) 乘该和。

原S.5.1一维远距离项写成 \(m^{2\bar\psi-2}n^{-2\bar\psi}\sum k^{-2\bar\psi}\)，遗漏了上述中心对数带来的一个m因子。不能在长记忆情形自动把这项丢入近距离误差。第6节说明原上界确实会失败。对于主要方法使用的m≈1/b，(16.8)更简洁，后面直接用它。

## 4. S.5.2：截断非线性项

文件15一致给出

\[
|EP(s_j)-H(s_j)|\le Ca_n,\qquad
E|P(s_j)-H(s_j)|^2\le C\{a_n^2+T_{\bar\psi}(N)\}.                \tag{16.10}
\]

q=1时 \(\ell\equiv0\)，所以I₂=0。q=2时，\(\ell,\ell',\ell''\) 在 \([0,1-\gamma/2]\) 上有界，真实H距两个截断端点有固定正距离。设 \(v=E(P-H)^2\)。投影不增加相对于H的误差，故

\[
E|\ell(P^\gamma)-\ell(H)|^2\le Cv.
\]

又有 \(|P^\gamma-P|\le |P-H|\mathbf1_{\{|P-H|\ge d_0\}}\)，从而 \(E|P^\gamma-P|\le v/d_0\)。Taylor公式给

\[
|E\{\ell(P^\gamma)-\ell(H)\}|\le C\{|E(P-H)|+v\}.
\]

对平均值使用Jensen，不假设不同j独立，得到

\[
EI_2^2\le C\{a_n^2+T_{\bar\psi}(N)\},\qquad
|EI_2|\le C\{a_n+T_{\bar\psi}(N)\}.                              \tag{16.11}
\]

这里aₙ→0，故aₙ²被aₙ吸收。S.5.2的输入矩现已由实际pilot验证；这一步不需要也未声称额外的1/M方差收益。

## 5. 合并并核对原4.2的速率

由平方和界、(16.8)、(16.11)及 \(|EI_1|\le CB_n\)，得到(16.3)–(16.4)。最后核对(16.1)的作用：

- 短记忆时，\(L^2T(n)/T(N)=bL^2\to0\)。
- 长记忆时，比值为 \(L^2b^{2\bar\psi}\to0\)，由(16.1)选足够大的固定k即可。
- 临界时，比值为 \(bL^3/\log N\)。若N≥√n，它不超过2bL²；若N<√n，则不超过 \(n^{-1/2}L^3/\log N\)。两种均趋于0。

所以(16.5)成立。相应条件偏差结论直接来自(16.4)。在全工作区间短记忆的情形，取

\[
b=(nL^2)^{-1/(2p+1)}
\]

时，离散模型均值误差为更低阶，且

\[
\sqrt{E(\widehat s-s)^2}
 =O\left(n^{-p/(2p+1)}L^{1/(2p+1)}\right).                        \tag{16.12}
\]

这保留原4.2的一维尺度估计速率。全局短记忆对q=2自动成立；q=1要求 \(\sup_JH<3/4\)。不同H跨临界的统一表述应把T换成原始幂和/过渡因子，不能隐藏随阈值间隔变化的常数。

## 6. 原S.5.1的实际反例

取q=1、p=1、常数 \(H=7/8\)，所以 \(\psi=1/4\)。选光滑、非负、对称、在(-1,1)内严格正的核，使用局部常数权重。取

\[
b=n^{-1/2},\qquad m=\lfloor(4b)^{-1}\rfloor.
\]

满足原带宽条件、m≈1/b，并属于原S.5.1的 \(m\le1/(3b)\) 分支。取固定平均区间A，合并权重νᵢ非负、和为1、\(\max\nu_i\le C/n\)。加权测度 \(\sum_i\nu_i\delta_{t_i}\) 弱收敛到A上的均匀概率测度：对连续函数φ，每个局部加权平均与φ在中心的值相差至多其b尺度连续模，再对粗网格作Riemann和。

这里可以用内部A；严格按原一维 \(\Omega_\delta\cap(0,1)=(\delta,1)\) 平均也一样。靠近1时使用实际有效网格上的单侧局部常数权重：由于所选核在内部严格正，分母仍≥cnb，窗口长度仍O(b)，所以非负性、最大权重界与上述弱收敛均保留。删除两个尺度所需的固定个数末端无效基点不改变这些性质。若两个尺度各自保留其末端有效权重，二者分别仍有同一均匀弱极限和C/n最大权重界；以下交叉求和极限也不变。

常H下相关核恰为冻结核。对(16.7)除以L后，两个通道系数为
\(d_{n,1}=L^{-1}-(\log2)^{-1}\)、\(d_{n,2}=(\log2)^{-1}\)。远距离交叉相关展开和对数的二阶Hermite系数给

\[
\operatorname{Cov}\left(\sum_a d_{n,a}g_{i,a},\sum_b d_{n,b}g_{j,b}\right)
=\left\{2c^2\left(\frac{2^\psi-1}{\log2}+L^{-1}\right)^2+o(1)\right\}
 |i-j|^{-2\psi},\quad c=H(2H-1),                                 \tag{16.13}
\]

对 \(|i-j|\ge\varepsilon n\) 一致。余下高阶Hermite项为 \(O(|i-j|^{-4\psi})\)，交叉冻结误差更小。

近对角部分的绝对值经 \(\max\nu_i\le C/n\) 控制，乘n^{2ψ}后不超过
\(C(n^{2\psi-1}+\varepsilon^{1-2\psi})\)。因此先离开对角线用弱收敛，再让ε趋于0，得到严格正极限

\[
\frac{n^{2\psi}}{L^2}\operatorname{Var}I_1
\longrightarrow
2c^2\left(\frac{2^\psi-1}{\log2}\right)^2
\frac1{|A|^2}\iint_{A^2}|x-y|^{-2\psi}dxdy>0.                    \tag{16.14}
\]

所以实际方差为 \(\asymp L^2n^{-1/2}\)。但原S.5.1右侧第一项为 \(O(L^2n^{-3/4})\)，第二项为 \(O(L^2n^{-1})\)，整体小于实际方差一个幂阶。**原S.5.1的上界因此确实错误，而非仅仅证明不够详细。**

修正版(16.8)正好给 \(O(L^2n^{-1/2})\)。尽管引理错误，原4.2较宽的MSE目标仍可容纳这一项，因为(16.1)保证 \(L^2T(n)=o(T(nb))\)。这解释了为什么必须修引理，但本范围的主要尺度估计速率仍可保留。
