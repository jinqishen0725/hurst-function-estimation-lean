# 09　minimax下界的完整书面修复：实际中点网格上的KL估计

**后续进展（文件19/20）：** [任意有限阶矩](19_all_finite_loss_moments.md)和[p=1端点下界](20_p1_minimax_lower_bound.md)现已书面补齐所列一维短记忆范围的全部有限Lˢ匹配；下文有关p=1或s>2尚未完成的文字是本文件当时的范围记录。高维、s=∞及Lean形式化仍待完成。

**后续进展：** [文件18](18_full_domain_l2_minimax.md)已补齐所列一维短记忆分支的全域MSE及同一函数类上1≤s≤2的minimax匹配；本文件的内部证明或原先缺口记录不包含这项后续边界论证。p=1下界、s>2匹配上界和高维仍待证。

对应：Proposition 8.1与Theorem 3.1。本文件补上此前作为条件保留的实际mBm KL界，并把它接到完整下界。这里证明的是普通数学结论，尚未转为Lean。原始依据：[正文](../19-AOS1825.pdf)、[补充材料](../suppdf_1.pdf)。

**结果。** 修复谱归一化、bump和分离半径，并正确处理首个半步长后，原文一维p>1、1≤s<∞的minimax下界速率

\[
(n\log^2n)^{-p/(2p+1)}
\]

可以保留。证明直接使用Definition 1.1的实际协方差，允许H−1/2正负变化；不再把“KL足够小”作为未证明假设。这个下界不认证文章的上界、CLT或更高维最优性。

## 1. 模型、观察网格和需要证明的KL界

固定σ>0，观察

\[
X(t_j),\qquad t_j=(j-1/2)/n,\quad j=1,\ldots,n.
\]

记P_H^{(n)}为Definition 1.1的一维零均值Gaussian观测分布。令H_0≡1/2，并设H可微且

\[
\sup_{0<t<1}|H(t)-1/2|\le a_n,\qquad
\sup_{0<t<1}|H'(t)|\le b_n,\qquad
(a_n+b_n)\log(2n)\to0. \tag{9.1}
\]

本证明同样适用于Lipschitz H，把第二个条件解释为Lipschitz常数界。

**定理9.1（修复后的Proposition 8.1）。** 存在固定常数C，使充分大的n满足

\[
\boxed{\operatorname{KL}(P_H^{(n)}\|P_{H_0}^{(n)})
\le C(na_n^2+b_n^2)\log^2(2n).} \tag{9.2}
\]

C不依赖n、H、a_n、b_n或σ；“充分大”只要求后面列出的统一小量条件成立。因此同一a_n、b_n控制的全部候选H可同时应用本界。用log n代替log(2n)只改变常数。

## 2. 归一化正确的Hilbert空间表示

令

\[
D(h)^2=\int_{\mathbb R}\frac{1-\cos\xi}{|\xi|^{2h+1}}d\xi,
\quad
F_h(t)(\xi)=\frac{e^{it\xi}-1}{\sqrt2D(h)|\xi|^{h+1/2}}.
\]

把这些复函数视为实Hilbert空间中的元素，内积取Re∫f overline(g)。对于0<h<1、0≤t≤1，它们属于L²；F_h(0)=0。

直接取实部、缩放积分得到

\[
\langle F_h(s),F_k(t)\rangle
=B(h,k)\{s^{h+k}+t^{h+k}-|s-t|^{h+k}\}, \tag{9.3}
\]
\[
B(h,k)=\frac{D((h+k)/2)^2}{2D(h)D(k)}.
\]

这恰是论文C(s,t)/σ²在H(s)=h、H(t)=k时的公式。其归一化来自√2；少它会使Brownian基准方差翻倍。

以下把h、k限制在J=[3/8,5/8]。D及其所需参数导数在J上有界，且D有正下界：对D²的积分求导只增加log|ξ|的幂，近0及无穷处都由固定可积幂函数控制。因此B和B的一阶参数导数统一有界。

同理，h↦F_h(t)在L²中连续可微，而且

\[
\partial_hF_h(t)=-(D'(h)/D(h)+\log|\xi|)F_h(t),
\quad
\sup_{h\in J,\ 0\le t\le1}\|\partial_hF_h(t)\|_2\le C. \tag{9.4}
\]

验证统一支配：|e^{itξ}−1|≤min(2,|ξ|)；导数模平方近0由C|ξ|^{-1/4}(1+|log|ξ||²)控制，尾部由C|ξ|^{-7/4}(1+log²|ξ|)控制。这也严格支持后面使用的参数积分，不需要为复函数选择一个与ξ无关的均值定理中间点。

## 3. 在实际中点网格上白化Brownian基准

令t_0=0，ℓ_j=t_j−t_{j-1}，则

\[
\ell_1=1/(2n),\qquad\ell_j=1/n\quad(j\ge2).
\]

把观测作相同的可逆线性变换

\[
Y_j=\frac{X(t_j)-X(t_{j-1})}{\sigma\sqrt{\ell_j}},\qquad X(t_0):=0.
\]

X(t_0)是人为加入的确定性零，不需要额外观察。该变换是n维观测向量的可逆下三角变换。H_0=1/2时(9.3)为min(s,t)，所以Y的协方差恰为I_n。由同一可逆变换下密度比的不变性，原观测的KL等于Y分布相对于N(0,I_n)的KL。

写h_j=H(t_j)，并任选h_0=h_1。定义Hilbert空间中的

\[
U_j=\ell_j^{-1/2}\{F_{h_j}(t_j)-F_{h_j}(t_{j-1})\},
\]
\[
V_j=\ell_j^{-1/2}\{F_{h_j}(t_{j-1})-F_{h_{j-1}}(t_{j-1})\}. \tag{9.5}
\]

V_1=0。Y的真实协方差矩阵Σ满足

\[
\Sigma_{jk}=\langle U_j+V_j,U_k+V_k\rangle.
\]

令A_{jk}=⟨U_j,U_k⟩、Q_{jk}=⟨U_j,V_k⟩、R_{jk}=⟨V_j,V_k⟩。于是

\[
E:=\Sigma-I=(A-I)+Q+Q^T+R. \tag{9.6}
\]

以下每一项都来自实际H的协方差，不是替代的统计模型。

## 4. 冻结增量矩阵A

本节记a=a_n、b=b_n、L=log(2n)，并取n充分大，使a≤1/8、aL≤1、b≤1。

### 4.1 对角项

由(9.3)在h=k时B(h,h)=1/2，

\[
A_{jj}=\ell_j^{2h_j-1}.
\]

因为|2h_j−1|≤2a、|log ℓ_j|≤L，使用|e^x−1|≤e^{|x|}|x|可得

\[
|A_{jj}-1|\le C aL. \tag{9.7}
\]

这包含首个半步长，没有把它错误地按1/n处理。

### 4.2 非对角项，包括相邻接触区间

对j≠k，区间I_j=[t_{j-1},t_j]与I_k的内部不相交。设α=h_j+h_k∈[1−2a,1+2a]。对(9.3)取两侧时间差分，其中仅−|s−t|^α贡献非零项，得到

\[
A_{jk}=\frac{B(h_j,h_k)\,\alpha(\alpha-1)}{\sqrt{\ell_j\ell_k}}
\int_{I_j}\int_{I_k}|s-t|^{\alpha-2}dsdt. \tag{9.8}
\]

若两区间只在端点接触，仍可使用此式：先把其中一个端点缩进ε>0，再令ε↓0。角点附近二维积分可由∫_0^C r^{α-1}dr控制，α≥3/4，故统一有限；矩形差分的边界值也连续收敛。α=1时积分仍有限，前面的α−1使两侧均为0。

令l=|j−k|。缩放x=ns、y=nt后，两区间长度为1或1/2，且1/√(ℓ_jℓ_k)≤2n。

- l=1时，它们接触或更远，缩放后的积分统一有界，可用∫_0^1∫_0^1(x+y)^{α−2}dxdy控制。
- l≥2时，两区间的缩放距离至少l−1≥l/2，故该积分≤C l^{α−2}。

因此对全部l≥1，

\[
|A_{jk}|\le C a\,n^{1-\alpha}l^{\alpha-2}
=\frac{Ca}{l}(l/n)^{\alpha-1}\le\frac{Ca}{l}. \tag{9.9}
\]

最后一步使用1≤l≤n以及|α−1|≤2a、a log(2n)≤1；最坏因子n^{2a}有固定上界。这也处理H−1/2为负的情形。

由(9.7)、(9.9)，

\[
\|A-I\|_F^2\le Cna^2L^2,\qquad
\max_j\sum_k|A_{jk}-1_{j=k}|\le CaL. \tag{9.10}
\]

这里分别使用Σ_{l≥1}l^{-2}<∞和Σ_{l≤n}l^{-1}≤1+log n。

## 5. H变化项R与关键混合项Q

### 5.1 R只需Hilbert空间范数界

对j≥2，|h_j−h_{j-1}|≤bℓ_j。由(9.4)及参数微积分基本定理，

\[
\|V_j\|_2\le Cb\sqrt{\ell_j}\le Cb/\sqrt n.
\]

j=1因V_1=0同样成立。因此

\[
|R_{jk}|\le Cb^2/n,\quad
\|R\|_F^2\le Cb^4,\quad
\max_j\sum_k|R_{jk}|\le Cb^2. \tag{9.11}
\]

### 5.2 时间差分的参数导数界

记x^α log x在x=0处为0。若x,y均为网格1/(2n)的非负整数倍、x,y≤1、|x−y|≤1/n，则对|α−1|≤2a有

\[
|x^\alpha-y^\alpha|\le C/n,\qquad
|x^\alpha\log x-y^\alpha\log y|\le CL/n. \tag{9.12}
\]

**证明。** x,y>0时，中间点属于[1/(2n),1]，故x^{α−1}≤(2n)^{2a}≤e²且|log x|≤L。对x^α和x^α log x使用导数界与均值定理即可。一个端点为0时，另一个属于[1/(2n),1/n]，直接代入给出相同界；均为0时显然。∎

记K(s,t;h,v)=⟨F_h(s),F_v(t)⟩，并令α=h+v。由(9.3)，

\[
K(s_1,t;h,v)-K(s_0,t;h,v)
=B(h,v)\{s_1^\alpha-s_0^\alpha-|s_1-t|^\alpha+|s_0-t|^\alpha\}. \tag{9.13}
\]

其中t^α项先精确消去。对v求导后，得到B_v乘括号，加B乘同样四个x^α log x项。对s_1=t_j、s_0=t_{j-1}、t=t_{k-1}，四个距离全在1/(2n)网格上，对应两个距离之差均≤1/n。B、B_v有统一界，故(9.12)给出

\[
\left|\partial_v[K(t_j,t_{k-1};h_j,v)
-K(t_{j-1},t_{k-1};h_j,v)]\right|\le CL/n. \tag{9.14}
\]

该界对v位于h_{k-1}与h_k之间一致。

### 5.3 混合项的真实量级

对k≥2，参数积分给出精确等式

\[
Q_{jk}=\frac1{\sqrt{\ell_j\ell_k}}
\int_{h_{k-1}}^{h_k}\partial_v
[K(t_j,t_{k-1};h_j,v)-K(t_{j-1},t_{k-1};h_j,v)]dv.
\]

利用1/√(ℓ_jℓ_k)≤2n、|h_k−h_{k-1}|≤b/n和(9.14)，

\[
\boxed{|Q_{jk}|\le CbL/n.} \tag{9.15}
\]

k=1时Q_{j1}=0。于是

\[
\|Q\|_F^2\le Cb^2L^2,\qquad
\max_j\sum_k|Q_{jk}|+\max_k\sum_j|Q_{jk}|\le CbL. \tag{9.16}
\]

这就是此前未闭合的关键步骤。若只对U、V使用Cauchy–Schwarz，会得到每项O(b/√n)，进而多出一个n；显式时间差分中常数项的消去提供了所需的额外n^{-1/2}。

## 6. 真实协方差矩阵的算子范数与Frobenius界

由(9.6)、(9.10)、(9.11)、(9.16)，

\[
\|E\|_F^2\le C\{na^2L^2+b^2L^2+b^4\}
\le C(na^2+b^2)L^2, \tag{9.17}
\]

最后一步用b≤1、L≥1。E实对称，其算子范数不超过最大绝对行和，故

\[
\|E\|_{op}\le C\{(a+b)L+b^2\}\to0. \tag{9.18}
\]

特别地充分大的n有‖E‖op≤1/2，Σ=I+E严格正定。设λ_j为E的特征值。Gaussian密度计算与|λ_j|≤1/2给出

\[
\begin{aligned}
\operatorname{KL}(P_H^{(n)}\|P_{H_0}^{(n)})
&=\frac12\sum_j\{\lambda_j-\log(1+\lambda_j)\}\\
&\le\frac12\sum_j\lambda_j^2
\le C(na^2+b^2)L^2.
\end{aligned}
\]

不等式由0≤λ−log(1+λ)=∫_0^λ t/(1+t)dt≤λ²推出。至此定理9.1已证，同时处理了实际中点网格和实际Gaussian矩阵的非退化性。∎

## 7. 修复后的完整Theorem 3.1

定义合法参数类

\[
\mathcal H_p(M)=\{H\in\mathcal H^p((0,1),M):0<H(t)<1\}.
\]

**定理9.2。** 对任意p>1、M>0、s∈[1,∞)、γ∈(0,1)，存在δ>0，只依赖p、M、s、γ，使

\[
\boxed{\liminf_{n\to\infty}\inf_{\widetilde H_n}
\sup_{H\in\mathcal H_p(M)}P_H^{(n)}
\left\{\|\widetilde H_n-H\|_s>
\delta(n\log^2n)^{-p/(2p+1)}\right\}>\gamma.} \tag{9.19}
\]

结论甚至对限制在固定区间[3/8,5/8]内的H子类成立。σ取任意固定正值，不改变δ的选择。

### 7.1 合法光滑候选函数和码本

取固定非零、非负φ∈C_c^∞(R)，支撑在[−1/2,1/2]，例如文件07中修正后的exp(−1/(1/4−x²))。令ε>0为之后选择的固定小常数，并设

\[
H_θ(t)=\frac12+\varepsilon m^{-p}\sum_{j=1}^m
\theta_j\phi(mt-j+1/2),\qquad\theta\in\{0,1\}^m. \tag{9.20}
\]

各bump支撑内部不交，在端点所有阶导数为零。文件07第2节的跨格Hölder证明给出一个只依赖p、φ的C_p，使全部候选函数的论文Hölder半范数≤C_pε，且

\[
a_n=\varepsilon\|\phi\|_\infty m^{-p},\qquad
b_n=\varepsilon\|\phi'\|_\infty m^{1-p}. \tag{9.21}
\]

选ε≤M/C_p并进一步缩小，即可保证候选函数合法且位于[3/8,5/8]。这一选择对m和θ一致。

贪心二进制打包给出Θ_m⊂{0,1}^m，满足不同码字距离>m/8，且

\[
\log|\Theta_m|\ge c_0m,\qquad c_0=\log2-h(1/8)>0.
\]

非重叠支撑上的精确积分给出

\[
\|H_θ-H_{θ'}\|_s\ge d_s\varepsilon m^{-p},\qquad
 d_s=8^{-1/s}\|\phi\|_s>0. \tag{9.22}
\]

### 7.2 KL不再是假设

取

\[
x_n=(n\log^2(2n))^{1/(2p+1)},\qquad m=\lceil x_n\rceil.
\]

由于p>1，(a_n+b_n)log(2n)→0，故定理9.1可以对所有θ一致应用，得到

\[
\operatorname{KL}(P_{H_θ}^{(n)}\|P_{1/2}^{(n)})
\le C_p'\varepsilon^2\{nm^{-2p}+m^{2-2p}\}\log^2(2n). \tag{9.23}
\]

除以log|Θ_m|，第一项利用m^{2p+1}≥n log²(2n)控制，第二项利用

\[
m^{1-2p}\log^2(2n)\to0
\]

控制。因此存在只依赖p、φ的C_p''，使

\[
\limsup_n\frac{\max_θ\operatorname{KL}(P_{H_θ}^{(n)}\|P_{1/2}^{(n)})}{\log|\Theta_m|}
\le C_p''\varepsilon^2. \tag{9.24}
\]

### 7.3 Fano、严格风险阈值与所有量词

令J均匀取码本标签，并按该标签生成观测。互信息满足

\[
I(J;X)\le |\Theta_m|^{-1}\sum_θ\operatorname{KL}(P_{H_θ}^{(n)}\|P_{1/2}^{(n)}).
\]

对任意解码器，Fano的熵分解H(J|X)≤log2+P_e log|Θ_m|给

\[
P_e\ge1-\frac{I(J;X)+\log2}{\log|\Theta_m|}. \tag{9.25}
\]

取ε>0足够小，使它既满足Hölder及值域约束，又满足C_p''ε²<(1−γ)/2。于是所有解码器错误概率的极限下界至少为1−C_p''ε²>γ；不等式与解码器无关。

对任意估计量Htilde_n，用Ls距离选最近候选函数作为解码器，并按固定标签顺序打破平局。由(9.22)，解码错误必然蕴含

\[
\|\widetilde H_n-H_J\|_s\ge d_s\varepsilon m^{-p}/2.
\]

令Δ_n=d_s ε m^{-p}/3。因Δ_n严格小于上述半分离距离，平均估计风险P{‖Htilde_n−H_J‖_s>Δ_n}至少等于解码错误概率。它又不大于合法参数类上的风险上确界。

由于m/x_n→1且log(2n)/log n→1，

\[
\frac{\Delta_n}{(n\log^2n)^{-p/(2p+1)}}\to d_s\varepsilon/3>0.
\]

取δ=d_s ε/6，则最终δ(n log²n)^{-p/(2p+1)}≤Δ_n。于是所需风险下界对每个估计量一致成立，可以取估计量下确界和n的下极限，得到(9.19)的严格大于γ。δ只依赖s、p、M、γ和固定选定的bump；bump可预先固定，不引入额外参数依赖。∎

## 8. 这次修复了什么，保留了什么

- 修复了谱表示缺少1/2：在特征函数分母中使用√2。
- 在原始中点网格直接工作：首段长度1/(2n)，按真实长度白化，不再略过网格变化。
- 以L²参数积分替换有歧义的复值均值定理中间点，并允许H−1/2有正负变化。
- 对相邻接触区间单独证明可积性，避免把非相邻导数界直接用于接触情形。
- 补上实际混合矩阵项O(b_n log n/n)，从而完整获得Frobenius界和算子范数小量。
- 以合法光滑bump、跨格Hölder控制和小于半分离的风险阈值完成原下界；显式选择ε处理“任意γ<1”。

因此，此前文件07中条件(7.6)现在由定理9.1证明，不再是悬空前提。原一维minimax下界速率得以保留。**这里的“完整”指上述下界的书面证明链完整；不是整篇论文已经证明，也不是已经通过Lean内核验证。**


## 9. 有限样本交叉检查

[数值记录](../verification/minimax_kl_checks.json)直接按Definition 1.1构造中点网格协方差，检查Brownian、正负常数扰动、正弦扰动和光滑bump扰动，共15个例子（n=64、128、256）。所有例子都通过：Σ=A+Q+Qᵀ+R、A的精确对角公式、Brownian白化为I、Gaussian KL与谱公式及平方界。最大矩阵分解误差约3.4×10^{-16}。

这些是公式的数值交叉检查，不证明统一渐近界；统一界的依据是第4–6节的逐项不等式。可用[检查脚本](../scripts/minimax_kl_checks.py)重跑。尚未进行Lean形式化或独立同行审阅。
