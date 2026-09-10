# 20. p=1端点下界：用统一正谱下界替代趋近单位阵

对应：Proposition 8.1、Theorem 3.1的p=1扩展，以及Remark 3.4(ii)在q=p=1时的minimax断言。复用[文件09](09_minimax_lower_bound_complete.md)的真实中点网格谱表示、白化和逐项矩阵估计，以及[文件07](07_bump_packing_and_lower_bound.md)的打包/Fano归约。

**结果。** 原Theorem 3.1本身只写p>1；以下补出p=1的下界，并在q=1、固定短记忆函数类上接合[文件19](19_all_finite_loss_moments.md)的上界。无需让packing幅度随log n缩小，速率保留为(n log²n)⁻¹ᐟ³。关键是换掉此前过强的“整块协方差必须趋近I”要求；实际Gaussian KL只需要一个统一正的最小特征值。

这是普通数学证明，尚未转Lean。它加强了文件09中使用的充分条件，不是对原Proposition 8.1有效范围的否定。

## 1. 需要加强的KL命题

令 \(L=\log(2n)\)，观察点仍是 \(t_j=(j-1/2)/n\)。令

\[
a=\|H-1/2\|_\infty,\qquad b=\operatorname{Lip}(H).
\]

**定理20.1。** 存在正常数c₀,b₀,C，使n≥2、aL≤c₀、b≤b₀时，真实观测分布满足

\[
\operatorname{KL}(P_{H,\sigma}^{(n)}\|P_{1/2,\sigma}^{(n)})
 \le C(na^2+b^2)L^2.                                           \tag{20.1}
\]

常数与n、H、σ无关。取c₀足够小，自动使H落在[3/8,5/8]。特别地，此处允许b为固定的小正常数；**不要求bL→0**。

## 2. 保留真实Gaussian特征分解

使用文件09中的实Hilbert空间特征

\[
F_h(t)(\xi)=\frac{e^{it\xi}-1}{\sqrt2D(h)|\xi|^{h+1/2}},\qquad
D(h)^2=\int_{\mathbb R}\frac{1-\cos\xi}{|\xi|^{2h+1}}d\xi.
\]

该文件已证明 \(\sup_{h\in[3/8,5/8],\,0\le t\le1}\|\partial_hF_h(t)\|_2\le C_F\)。设t₀=0、ℓⱼ=tⱼ−tⱼ₋₁；首段ℓ₁=1/(2n)，其他段1/n。白化观测为 \((X(t_j)-X(t_{j-1}))/(\sigma\sqrt{\ell_j})\)，Brownian基准协方差恰是I。

写hⱼ=H(tⱼ)，取h₀=h₁，定义

\[
U_j=\ell_j^{-1/2}\{F_{h_j}(t_j)-F_{h_j}(t_{j-1})\},\quad
V_j=\ell_j^{-1/2}\{F_{h_j}(t_{j-1})-F_{h_{j-1}}(t_{j-1})\}.       \tag{20.2}
\]

将U,V看成从Rⁿ到此Hilbert空间的列算子，Ueⱼ=Uⱼ、Veⱼ=Vⱼ。于是

\[
A=U^*U,\quad R=V^*V,\quad Q=U^*V,\quad
\Sigma=(U+V)^*(U+V)=A+Q+Q^*+R.                                 \tag{20.3}
\]

这都是实际协方差的恒等式，未替换为冻结模型。

## 3. 冻结部分接近I，变化部分只需算子范数小

文件09第4节的证明只使用aL有界，不使用bL→0。它给出

\[
\|A-I\|_{\rm op}\le C_A aL,\qquad
\|A-I\|_F^2\le C_A n a^2L^2.                                  \tag{20.4}
\]

取c₀使C_Ac₀≤1/4，于是A的特征值在[3/4,5/4]。

对变化列，V₁=0，其他列由参数积分及Lipschitz H给出

\[
\|V_j\|_2\le C_F b\sqrt{\ell_j}.
\]

因此

\[
\|V\|_{\rm op}\le\|V\|_{\rm HS}
 =\left(\sum_j\|V_j\|_2^2\right)^{1/2}
 \le C_F b\left(\sum_j\ell_j\right)^{1/2}\le C_F b.             \tag{20.5}
\]

取b₀≤min(1,1/(4C_F))，即有 \(\|V\|_{\rm op}\le1/4\)。对任意x∈Rⁿ，正向和反向三角不等式给出

\[
(\sqrt{3/4}-1/4)\|x\|_2
 \le\|(U+V)x\|_2
 \le(\sqrt{5/4}+1/4)\|x\|_2.
\]

所以

\[
\boxed{\tfrac14I\preceq\Sigma\preceq\tfrac94I.}                \tag{20.6}
\]

常数选择留有余量。这一步不需要Q的逐行绝对和趋于0：直接利用实际Gram算子结构，避免粗略的bL上界。

## 4. Frobenius估计仍保留原来需要的阶

文件09第5节的逐项混合估计，在aL≤c₀≤1、b≤b₀≤1时仍完全适用：

\[
|Q_{jk}|\le CbL/n,\qquad |R_{jk}|\le Cb^2/n.
\]

其依据是对真实协方差核先取时间差分，再对H参数求导；网格相邻幂差及对数幂差分别为O(1/n)、O(L/n)。该计算不要求bL小。由此

\[
\|Q\|_F^2\le Cb^2L^2,\qquad \|R\|_F^2\le Cb^4.
\]

结合(20.3)、(20.4)，

\[
\|\Sigma-I\|_F^2
 \le C(na^2L^2+b^2L^2+b^4)
 \le C(na^2+b^2)L^2.                                           \tag{20.7}
\]

最后使用b≤1、L≥1。

对于λ∈[1/4,9/4]，函数f(λ)=λ−1−logλ满足f(1)=f'(1)=0，且f''(λ)=λ⁻²≤16。因此Taylor公式给0≤f(λ)≤8(λ−1)²。实际白化矩阵正定，由Gaussian KL公式、(20.6)及(20.7)，

\[
\operatorname{KL}(N(0,\Sigma)\|N(0,I))
 =\frac12\sum_jf(\lambda_j)
 \le4\|\Sigma-I\|_F^2\le C(na^2+b^2)L^2.
\]

对原观测作同一可逆线性变换不改变KL，故定理20.1得证。∎

注意：这不声称Σ−I在p=1构造下趋于0；统一的谱区间已经足够支持KL二次界。

## 5. p=1的合法packing与KL/Fano计算

固定M>0以及 \(0<\eta<1/2<h_*<1\)，令

\[
\mathcal F_1=\{H\in\mathcal H^1((0,1),M):\eta\le H\le h_*\}.
\]

原文p=1的半范数条件是H可微且 \(|H'(x)-H'(y)|\le M\)。取文件07中的固定非零非负光滑bump φ，支撑于[−1/2,1/2]，并令

\[
m=\lceil(nL^2)^{1/3}\rceil,\qquad
H_\theta(t)=\frac12+\epsilon m^{-1}\sum_{j=1}^m
 \theta_j\phi(mt-j+1/2).                                       \tag{20.8}
\]

每点至多一个bump非零；拼接处所有导数为0。因此

\[
a_n\le\epsilon\|\phi\|_\infty/m,\qquad
b_n\le\epsilon\|\phi'\|_\infty,\qquad
\sup_{x,y}|H_\theta'(x)-H_\theta'(y)|
 \le2\epsilon\|\phi'\|_\infty.                                 \tag{20.9}
\]

选择固定ε>0足够小，同时满足2ε||φ'||∞≤M、ε||φ'||∞≤b₀，以及值域限制和[3/8,5/8]限制。于是全部候选属于同一个固定参数类。并且aₙL→0；bₙ不需要趋于0，所以定理20.1最终对全部θ一致适用。

文件07的二进制码本满足Hamming距离>m/8、log|Θₘ|≥c₁m。对任意固定1≤s<∞，非重叠支撑给出

\[
\|H_\theta-H_{\theta'}\|_{L^s(0,1)}
 \ge d_s\epsilon/m,\qquad d_s=8^{-1/s}\|\phi\|_s>0.             \tag{20.10}
\]

以H₀≡1/2作KL参考，定理20.1给出

\[
\max_\theta\operatorname{KL}(P_{H_\theta,\sigma}^{(n)}\|P_{1/2,\sigma}^{(n)})
 \le C\epsilon^2(nm^{-2}+1)L^2.
\]

除以码本对数，得到

\[
\frac{\max_\theta\operatorname{KL}}{\log|\Theta_m|}
 \le C'\epsilon^2\left(\frac{nL^2}{m^3}+\frac{L^2}{m}\right),
\qquad \limsup_n\frac{\max_\theta\operatorname{KL}}{\log|\Theta_m|}
 \le C'\epsilon^2.                                             \tag{20.11}
\]

这里nL²/m³≤1，L²/m→0。固定任意γ∈(0,1)，进一步把ε选到C'ε²<(1−γ)/2。Fano给出所有解码器的错误概率极限下界大于γ。

对任意函数估计量选最近候选作为解码器；解码错误蕴含估计误差至少为(20.10)的一半。取严格小于半分离的阈值d_sε/(3m)，并利用m/(nlog²n)¹ᐟ³→1，得到某个δ>0使

\[
\boxed{\liminf_n\inf_{\widetilde H}\sup_{H\in\mathcal F_1}
 P_{H,\sigma}^{(n)}\left\{\|\widetilde H-H\|_{L^s(0,1)}
 >\delta(n\log^2n)^{-1/3}\right\}>\gamma.}                       \tag{20.12}
\]

可以取δ=d_sε/6。所有常数选择在n、θ、估计量之前完成；σ任意固定正值，KL界与σ无关。∎

## 6. 接合p=1上界与主要结论

若另有固定h_*<3/4，q=1短记忆的实际上界覆盖p=1：原类给出的H全域Lipschitz，取局部常数权重和b=(nlog²n)⁻¹ᐟ³。文件19已给任意有限阶误差矩及全部有限Lˢ上界。因此，对每个1≤s<∞，

\[
\inf_{\widetilde H}\sup_{H\in\mathcal F_1}
 E\|\widetilde H-H\|_{L^s(0,1)}^2
 \asymp(n\log^2n)^{-2/3}.                                      \tag{20.13}
\]

未知正的常尺度时也成立：上界使用文件19的实际尺度平均矩，σ一致性来自尺度不变性；下界固定一个σ子模型。由此补上Remark 3.4(ii)中p=q=1的匹配缺口。

(20.12)的下界本身不需要h_*<3/4；该条件只用于当前的一阶差分匹配上界。原定理3.1的p>1下界也保持有效，现可在上述固定值域类内扩展到p≥1。

## 7. 此前障碍究竟是什么

此前的推导用 \(\|\Sigma-I\|_{\rm op}\le C(a+b)L+Cb^2\) 强求其趋于0。p=1的固定幅度packing使b为常数，所以这条充分条件失败；缩小幅度又会丢失目标速率。

这不构成下界错误的反例。新证明把两件事分开：用aL→0控制冻结部分，用 \(\|V\|_{\rm op}\le Cb\) 保证真实协方差远离奇异；然后保留含b²L²的Frobenius界用于KL。该项除以packing熵m后趋于0，因此不妨碍Fano。

**当前剩余范围：** 本文件没有高维下界、s=∞风险或非规则网格/非恒定尺度证明；新增矩阵和Fano论证均尚未转Lean。


## 8. 实际p=1矩阵的有限检查

检查n=64、128、256、512以及三种p=1光滑bump码字，共12组。构造幅度ε固定，Lipschitz上界不随n缩小；核对真实Σ=A+Q+Qᵀ+R、Gram谱上下界及KL二次界。最大矩阵重构误差约1.7×10⁻¹⁶，实际Σ的特征值位于约[0.9957,1.0033]。有限样本中接近I并不是证明所需前提，也不能据此声称它渐近趋于I。

记录见[有限检查](../verification/minimax_endpoint_moment_checks.json)。这些计算用于公式交叉核对，不替代解析证明，不计为Lean验证。
