# 24. 后续端点、中心化与 Lean 验收约束

日期：2026-09-14。与[文件22](22_long_memory_repair_lean_handoff.md)、[文件23](23_spectral_probability_support.md)一起阅读。

本文补充容易在形式化收尾时被省略的证明，并给出未知尺度的一组保守、可满足的多项式带宽条件。**以下是书面推导和接口说明，新组合尚未通过 Lean。** 当前任务不因此自动升级为整篇论文所有分支均已完成。

## 1. 必须保持一致的对象与归一化

记 \(h=f(t)\)、\(\psi=2-2h\in(0,1/2)\)、\(\delta_n=n^{-\gamma}\)、\(S_n=n\delta_n\)、\(m_n=\#I_n\)，不要用同一个 `b` 同时表示 H 的值域上界和带宽。

| 对象 | 精确定义或意义 | 常见误接及排除方法 |
|---|---|---|
| 原局部权重 | \(w_{n,i}\) | 最终 \(\sum_iw_{n,i}=1\)，不是 \(S_n\) |
| 缩放权重 | \(u_{n,i}=S_nw_{n,i}\) | 这是趋于等价核的量 |
| 二阶项谱权重 | \(S_n^{\psi-1}u_{n,i}=S_n^\psi w_{n,i}\) | 不得重复乘一次 \(S_n\) |
| 实际行加权矩阵 | \(A_n=S_n^{\psi-1}\operatorname{diag}(u_n)C_n\) | 一般非对称，不能直接使用 Hermitian 谱定理 |
| 自伴二次型矩阵 | \(B_n=S_n^{\psi-1}C_n^{1/2}\operatorname{diag}(u_n)C_n^{1/2}\) | 实谱来自它；\(C_n\) 可奇异 |
| 循环积分 | \(J_k\)，k≥2 | 需证明绝对可积；零测集上的对角值不影响积分 |
| 极限谱 | \(\lambda_{2j}=p_j,\lambda_{2j+1}=-q_j\) | 正负分别排序，允许插入零 |
| 极限二阶项 | \(Q=\sum_j\lambda_j(Z_j^2-1)\) | \(\operatorname{Var}Q=2\sum_j\lambda_j^2\) |
| H 的期望中心极限 | \(2S_n^\psi\log n(\widehat H_n-E\widehat H_n)\Rightarrow-Q\) | 必须保留负号和因子2 |

从实际观测空间到标准 Gaussian 谱空间通常只有**同分布**，不是函数逐点相等。先证明 `IdentDistrib`，再用变化样本空间的分布转移工具。

## 2. 有限多个坏行：无需额外数学假设

### 引理 E1：最终同律转移

设 \(X_n:(\Omega_n,P_n)\to\mathbb R\)、\(Y_n:(\Theta_n,R_n)\to\mathbb R\) 可测，且最终 \((P_n)_{X_n}=(R_n)_{Y_n}\)。若 \(Y_n\Rightarrow Q\)，则 \(X_n\Rightarrow Q\)。

**证明。** 对任意有界连续实函数 F，\(E_{P_n}F(X_n)=E_{R_n}F(Y_n)\) 最终成立，因此前者与后者具有相同极限。弱收敛的测试函数刻画即得结论。只需要最终等式；\(\Omega_n\) 与 \(\Theta_n\) 不必相同。

如果现有 Lean 转移定理要求每行同律，定义安全行 \(\widetilde X_n\)：在好行上取 \(X_n\)，在有限坏行上取常数0；谱侧也相应取零系数行。先证明安全行逐行同律，再用两次最终相等转移。不得为了满足接口而要求不存在的 `Fin 0` 元素。

### 引理 E2：最终事件合并的正确量词

证明通常分别得到 \(m_n>0\)、\(S_n\ge1\)、\(\delta_n>0\)、增量非退化、范数上界等最终事件。有限多个事件用过滤器的有限交或 `filter_upwards` 合并即可。

但 \(\forall k,\forall^{\rm eventually}n,P(k,n)\) 不等价于
\(\forall^{\rm eventually}n,\forall k,P(k,n)\)。固定幂数 k 的迹收敛、固定前缀 K 的尾界都只需要前一种量词；不要为了“统一 n”新增更强条件。

## 3. 直接可用的四阶余项界

### 引理 E3：实际带权四阶双和趋零

假设已有文件22的同一个 \(R_n\to\infty\)、\(\eta_n\to0\)，以及最终

\[
|u_{n,i}|\le U,\quad |\rho_{n,ij}|\le1,\quad
E_{2,n}=S_n^{2\psi-2}\sum_{ij}\rho_{n,ij}^2\le C_2,
\]

\[
d>R_n\implies |d^\psi\rho_{n,ij}-c|\le\eta_n,
\quad
S_n^{2\psi-2}m_n(2R_n+1)\to0.
\]

则有可直接形式化的不等式

\[
\begin{aligned}
0\le&S_n^{2\psi}\sum_{ij}|w_{n,i}w_{n,j}|\,|\rho_{n,ij}|^4\\
\le& U^2S_n^{2\psi-2}m_n(2R_n+1)
 +U^2(c+\eta_n)^2R_n^{-2\psi}C_2\longrightarrow0.             \tag{E1}
\end{aligned}
\]

证明为文件22 W8 的近远带分拆；写成绝对权重版本，可以处理负权重并直接控制整段 Hermite 尾项。这里 \(\eta_n\ge0\) 可由实际包络定义得到；若泛型接口不要求它非负，将 \(c+\eta_n\) 改成 \(|c|+|\eta_n|\)。

**如何从核误差得到 \(C_2\)。** 设 \(V_{n,ij}=S_n^\psi\rho_{n,ij}\)，R 为无权 Riesz 核。由 \(|V|^2\le2|V-R|^2+2|R|^2\)，

\[
E_{2,n}\le2\,\mathrm{meshEnergy}(V_n-R_n^{\rm kernel})+2C_{\rm ref}.
\]

第一项趋于0，所以例如 \(C_2=2+2C_{\rm ref}\) 是最终上界。不要从 \(\operatorname{Var}Q_n\) 的有符号权重双和逆推出此无权界。

令 \(R_g=g-H_2\)，已有正交 Hermite 展开给
\(|E[R_g(Y_i)R_g(Y_j)]|\le\|R_g\|_2^2|\rho_{ij}|^4\)。对有限加权和平方展开、交换有限和与积分，再用 (E1)，得到实际余项的 L² 收敛；无需逐个证明所有高阶 Hermite 项的 CLT。

## 4. 期望中心、真值中心与偏差漂移

### 引理 E4：中心变化的精确规则

若 \(a_n(X_n-c_n)\Rightarrow Z\)，且确定性 \(a_n(c_n-d_n)\to\beta\)，则
\(a_n(X_n-d_n)\Rightarrow Z+\beta\)。证明是精确分解后加上确定性收敛量。

所以文件22以 \(E\widehat H_n\) 为中心的结论，只有在
\(2S_n^\psi\log n(E\widehat H_n-h)\to0\) 时才能无漂移地改成真值中心。分布收敛本身不允许交换期望。

### 引理 E5：一组无需高阶偏差首项的真值中心条件

仍采用文件22的已知尺度模型。设局部平滑偏差已证明满足

\[
\left|\sum_iw_{n,i}f(t_i)-h\right|\le C\delta_n^s\quad(s>0),
\]

且实际归一化增量方差与冻结单位方差的误差为 \(e_n\to0\)。最终 \(e_n\le1/2\)，故 \(|\log(1+x)|\le2|x|\) 给

\[
\left|E\widehat G_n-(c_\sigma-2h\log n)\right|
\le C(\log n\,\delta_n^s+e_n).                              \tag{E2}
\]

定义 \(\alpha=(1-\gamma)\psi\)，则 \(S_n^\psi=n^\alpha\)。文件22条件已保证 \(n^\alpha e_n\to0\)。若再有

\[
\boxed{\alpha<\gamma s\quad\text{即}\quad
\gamma>\frac{\psi}{s+\psi},}                                \tag{E3}
\]

则 \(S_n^\psi\log n\,\delta_n^s\to0\)。结合 (E2)、文件22 W9 的投影 L¹ 误差，得到

\[
2S_n^\psi\log n(\widehat H_n-h)\Rightarrow-Q.                \tag{E4}
\]

这里 s 必须来自实际权重与正则性的已证偏差界。不能对任意次数 r 的局部多项式直接取 \(s=p\)。一个保守选择是 \(s=1\)：当 p≥1 时 f 在固定内部邻域局部 Lipschitz，权重再现常数且绝对和有界，故
\(|\sum_iw_i(f(t_i)-h)|\le C\delta_n\)。若要用更大的 s，另行核对局部多项式次数与导数条件。

**局部 Lipschitz 的证明边界。** 对仓库 p≥1 的 Hölder 类，p=1 时一阶导数的振荡受 M 控制，选定邻域内一个基点即可得到导数有界；1<p<2 时导数 Hölder 连续；p≥2 时一阶导数在紧内部邻域连续。分别由中值定理得到局部 Lipschitz。常数可依赖该固定模型和邻域；本文没有据此声称全类统一最优偏差常数。

若漂移有非零极限而不是趋零，应使用 E4 保留漂移。若漂移不收敛，就不能登记相应真值中心极限完成。

## 5. 未知尺度：通用传递与一组可行的保守速率

本节只处理 q1、固定未知常尺度 \(\sigma\ne0\)。记 \(s_\sigma=\log\sigma^2\)，令 \(\widehat s_n\) 为仓库实际 `q1LogScaleEstimator`，不是任意假设存在的辅助估计量。

### 引理 E6：不需要独立性的尺度 L¹ 传递

设 \(T_n\) 为 q1 校准函数在 \([0,1]\) 上的截断逆。由于校准函数斜率为 \(-2\log n\)，投影不扩张，有

\[
|T_n(x)-T_n(y)|\le\frac{|x-y|}{2\log n}\quad(n\ge2).
\]

定义使用同一份数据的已知和未知尺度估计器

\[
H_n^o=T_n(G_n-s_\sigma),\qquad
H_n^u=T_n(G_n-\widehat s_n).
\]

于是

\[
2S_n^\psi\log n\,E|H_n^u-H_n^o|
\le S_n^\psi E|\widehat s_n-s_\sigma|.                       \tag{E5}
\]

右侧趋零便给 L¹、依概率的小量，以及真实期望中心之间的小量。具体地
\(E|(H_n^u-EH_n^u)-(H_n^o-EH_n^o)|\le2E|H_n^u-H_n^o|\)。所以期望中心极限和满足 E3 时的真值中心极限均可传递。

全过程不要求 \(\widehat s_n\) 与 \(G_n\) 独立。仅知道二者各自边际极限也不能替代 (E5) 中的速率证明。

### 引理 E7：从当前已证 q1 尺度界提取一个显式多项式率

当前 `hurstHolder_q1_logScale_L1_lt_one` 的单位尺度版本给出

\[
E|\widehat s_n|\le
C\log n\sqrt{R_{1,n}/n+R_{2,n}/n}
 +\log n\,e_n,
\]

其中 \(R_{d,n}=\mathrm{firstStrideLongRowBound}(b,C_d,A_d,d,n)\)，d=1,2。见证常数均固定，不能让它们随 n 变化。由该行界的定义及 \(\lceil\sqrt n\rceil\le\sqrt n+1\)，

\[
R_{d,n}/n\le C_d'
\left(n^{-1/2}+n^{-1}+n^{2b-2}+e_{d,n}^2\right),            \tag{E6}
\]

其中固定 d 的幂吸收到常数。于是

\[
E|\widehat s_n|
\le C\left[\log n\,(n^{-1/4}+n^{b-1})
 +(1+\log(2n))^2(n^{-1}+n^{2b-2})\right].                  \tag{E7}
\]

目标为长记忆且 \(b\ge h>3/4\)，因此 \(0<1-b<1/4\)。各项均被常数乘
\((1+\log(2n))^2n^{-(1-b)}\) 控制。故得到保守但足够的界

\[
\boxed{E|\widehat s_n-s_\sigma|
\le C(1+\log(2n))^2n^{-(1-b)}.}                             \tag{E8}
\]

从单位尺度推广到 \(\sigma\ne0\) 使用已有 `q1LogScaleEstimator_scale_integral`，取 \(\Phi(x)=|x|\)。其权重和为1、两种 stride 特征非零的前提，要用实际平均权重再现和最终协方差范数下界消除；不能只写“尺度不影响结果”。

尺度估计使用的 pilot 带宽可取 \(\delta_{1,n}=n^{-1/2}\)，平均网格数取 \(M_n=\lceil\sqrt n\rceil\)。则最终 \(\delta_{1,n}\le1/2\)、\(n\delta_{1,n}\to\infty\)、\(M_n\delta_{1,n}\ge1\)，满足上述实际尺度定理的几何前提。此处 M_n 是平均中心数，不是活动行长 m_n，也不是 Hölder 常数 M。

### 推论 E8：已知尺度、未知尺度、真值中心的一组共同带宽

对最终局部统计量取 \(\delta_{2,n}=n^{-\gamma}\)，并要求

\[
\boxed{1-\frac{1-b}{\psi}<\gamma<1.}                        \tag{E9}
\]

因为 \(b\ge h\)，\((1-b)/\psi\le1/2\)，且该比例严格为正，所以区间非空，并且 \(\gamma>1/2\)。此时

\[
\alpha=(1-\gamma)\psi<1-b<2-2b,
\qquad \alpha<1/4<\gamma.
\]

第一式满足文件22的实际核网格条件及 (E8) 所需的 \(S_n^\psi E|\widehat s_n-s_\sigma|\to0\)，第二式满足 s=1 的 E3。因而，一旦文件22和23的已知尺度端点完成，本节实际尺度界按上述方式实例化，就同时得到

\[
2S_n^\psi\log n(H_n^u-EH_n^u)\Rightarrow-Q,
\qquad 2S_n^\psi\log n(H_n^u-h)\Rightarrow-Q.                \tag{E10}
\]

例如 \(h=0.9,b=0.95,\psi=0.2\)，取 \(\gamma=0.875\)；此时 \(\alpha=0.025<0.05=1-b\)。可配 \(f\equiv0.9\)、\(a=0.8,p=1,M=0,t=1/2,r=0\)、任意 \(\sigma\ne0\)，给出普通数学意义下的模型实例。Lean 中仍需实例化实际权重、观测和各个最终事件，而不只 `norm_num` 检查三个实数不等式。

**范围说明。** E8 是新补写的保守充分条件，未宣称最优，也未宣称所有满足文件22较宽带宽区间的未知尺度端点都已完成。它直接利用当前较粗但已证明的行界，避免把文件21更尖锐的书面速率未经核对就当作现成 Lean 定理。

## 6. 拟新增接口及实际验收顺序

以下名称仅为实现建议，均应在新模块中定义，不是现有 API。

| 拟新增结果 | 输入应保留什么 | 输出及禁止保留的内部前提 |
|---|---|---|
| `polyBandwidth_cutoff_and_envelope_direct` | h,b,M；0<γ<1；网格指数条件；最终活动集上界 | 构造 R、hcut、henv；无 γ<4h−3 |
| `actualQ1_trace_pow_tendsto_direct` | 普通模型、内部点、长记忆、可行带宽、k≥2 | 实际矩阵迹趋于 J_k；无 hPert/hFrozenPert/hcard |
| `weightedRieszSpectrum_exists` | 0<ψ<1/2、c>0、ω连续有界 | 存在有符号 λ；所有 HasSum；无预设 hRiesz |
| `secondChaosSeriesLaw_exists` | λ平方可和 | 存在概率空间、P、Q及完整 hQ；不要求任意预设空间承载 Q |
| `signedPowerSums_padded_data` | 所有 k≥2 幂和收敛、目标平方可和、行长趋∞ | 正负交错系数、逐坐标收敛、尾界、补零同律 |
| `actualQ1_quadratic_tendsto_direct` | 普通模型与文件22带宽条件 | 实际二阶统计量→构造的 Q；无 hRiesz/hQ/hwnn/hNegMass/hane |
| `actualQ1_log_tendsto_direct` | 同上 | 实际期望中心 log 极限；四阶余项在内部消除 |
| `actualQ1_estimator_tendsto_direct` | 同上；已知尺度 | 已知尺度期望中心 H 极限，保留 −Q |
| `actualQ1_unknown_long_tendsto_safe_rate` | 同一实际模型、σ≠0、E9、指定 pilot/平均网格 | 未知尺度期望中心和真值中心；E8 的实际界在内部消除 |

先让前两项完成，证明旧带宽矛盾已经被实际修复；随后完成谱、律及有符号匹配；最后连接 log、H 和可选的未知尺度充分条件。不要先改 `mainline_complete` 再填证明。

### 实现中需要逐项检查的事项

1. `Matrix.Norms.Frobenius` 必须是 W3–W5 的范数实例。矩阵默认范数和 `L2Operator` 范数不能通过同名 `‖·‖` 默默混用。
2. `powDelta_pos` 等当前标为 `private` 的辅助引理不能从新模块按普通公开名调用；把必要的短证明放进新公开辅助模块，或复用已经公开的等价定理。
3. 有符号谱采用全部幂和；不得把现有要求负谱质量趋零的 `signedMatching` 名字误读成一般有符号极限支持。
4. 分布极限可能位于不同概率空间；只需逐行或最终同律转移，不要求所有原始样本空间相同。
5. 保持每一个 `MemLp`、可测性和 `HasSum` 前提；不能只依赖 Lean 积分或无限和在不满足可积性时的默认值。
6. 文件22–24的书面证明都不是“获准外部文献定理”。这里的内部引理必须形式化或从现成 mathlib 定理正确推出。
7. 只完成非负权重特例时，必须保持特例标题；真实谱允许负项，不能通过改定义为绝对值来“完成”一般情况。
8. 未知尺度 E8 是保守速率的延伸；不要据此标记联合 pilot、高维或 minimax 的其余范围已完成。

### 每层的验证

编译新增模块后检查实际定理的完整类型，再检查 `#print axioms`。至少要验证三类模型/参数：

* 普通合法常数 H，验证最终定理确实可实例化；
* h 与 b 相距较大时，验证所宣称的带宽区间仍非空；
* 泛型有符号谱，包含正、负及重复绝对值，验证排序桥未偷偷要求非负。

原始 capstone 的反证文件应继续能编译：它是旧接口失败的证据，不能通过删除反证或把新定理接回旧假设消除审计问题。最终同步摘要时分别记录每个端点的范围及真实完成状态。

### 可直接交给接手 agent 的任务说明

请依次实施文件22–24的长记忆修复。先完成文件22 W1–W5，给出可满足带宽下的实际谱幂和极限；再按文件23 A–D 构造极限谱、Q 和一般有符号谱的收敛，优先消费现有 `centeredSpectralSquares_tendsto_secondChaos_of_padded_l2`。接着完成文件22 W8–W9，最后处理文件23 E 的极限性质；未知尺度按文件24 E6–E8作为单独端点验收。

每完成一层，请报告实际 Lean 定理名、完整剩余前提、编译结果，以及一个适用性或非空性检查。所有内部引理都必须在 Lean 中证明，不得新增占位公理、`sorry`，或以 `hRiesz`/`hQ`/`hwnn` 等未经证明的内部条件替代最终结论。若遇到库接口缺失，定位到本文最小引理，说明准确缺口并尝试其书面证明；不要把泛型算子论或概率论任务扩大成无关的库建设。不得仅凭聚合构建和公理审计通过就宣称整条主线完成。
