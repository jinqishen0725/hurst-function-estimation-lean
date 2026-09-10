# 统计与概率Lean复用记录

检查日期：2026-09-08。本项目保持Lean/mathlib v4.31.0。下表区分实际移植、源码调查和未来候选；外部文件中没找到占位符，不等于其传递依赖已经在本项目验证。

## 已直接使用

### mathlib：Gaussian、Gram矩阵与概率积分

本轮使用[mathlib v4.31.0](https://github.com/leanprover-community/mathlib4/tree/v4.31.0/Mathlib/Probability/Distributions/Gaussian)现有的多元Gaussian、线性像、协方差双线性型、Gaussian所有有限阶原始矩、无原子性，以及Gram矩阵的半正定性。

新模块[GaussianFinite.lean](Hurst/GaussianFinite.lean)定义真实概率测度

\[
P_v=\mathcal N(0,\operatorname{Gram}(v)),\qquad
\operatorname{Cov}_{P_v}(\langle a,X\rangle,\langle b,X\rangle)
=\left\langle\sum_i a_i v_i,\sum_j b_j v_j\right\rangle.
\]

已形式化线性统计量的均值、方差、Gaussian分布、所有有限阶原始矩，以及特征组合非零时的严格正方差和几乎处处非零。还形式化文件20使用的扰动步骤：若主项范数≥3‖a‖/4、扰动范数≤‖a‖/4，则真实Gaussian线性统计量的方差≥‖a‖²/4。

这些是一般Hilbert特征的结果。仍须把论文的谐和积分特征构造成该Hilbert空间的元素，并证明其具体估计。

第二批新增[GaussianLog.lean](Hurst/GaussianLog.lean)，复用mathlib的Gaussian加权幂积分、log与幂的渐近比较及可积性拼接，真正证明log平方的所有自然数阶绝对矩有限。先处理零点附近，再处理尾部；不是由原始矩或几乎处处非零推断。随后证明E log X²=log v+E log Z²，并传递到实际有限维模型，得到有限加权对数统计量的期望、含全部交叉协方差的方差和MSE分解。

### StatLean/Stat-Lean：一维及多元KL已实际移植

上游：[GaussianKL.lean](https://github.com/StatLean/Stat-Lean/blob/855b6afb69fead1bef066111732ed44df181040e/StatLean/Minimaxity/ForMathlib/GaussianKL.lean)。固定提交`855b6afb69fead1bef066111732ed44df181040e`，原工具链v4.29.1。实际许可证文本为Apache-2.0，已保留[LICENSE](third_party/StatLean/LICENSE)和[来源说明](third_party/StatLean/NOTICE.md)。

本地[GaussianKL.lean](Hurst/GaussianKL.lean)移植其等方差均值变化公式，并新增零均值方差变化公式：对v>0，

\[
D\bigl(\mathcal N(0,v)\,\|\,\mathcal N(0,1)\bigr)
=\frac{v-1-\log v}{2}.
\]

这里v是方差。Lean等式左边是mathlib的真实`InformationTheory.klDiv`，右边用`ENNReal.ofReal`表示；证明包含密度比、绝对连续性、对数似然比的可积性及积分计算。没有把KL公式直接放进假设。

第二批继续移植同一固定提交中的数据处理不等式、两因子乘积KL及多元Gaussian KL。所选传递依赖均在本项目v4.31.0中编译通过；没有引入整个StatLean库。对应[KLDataProcessing](Hurst/KLDataProcessing.lean)、[KLProduct](Hurst/KLProduct.lean)、[GaussianKLMulti](Hurst/GaussianKLMulti.lean)。多元文件直接复用第一批已证明的一维方差变化公式，删去了本任务不需要的均值变化推论。

新增[GaussianKLBound](Hurst/GaussianKLBound.lean)将真实D(N(0,A)‖N(0,I))接到既有spectralKL，并在每个特征值满足|λᵢ−1|≤1/2时证明KL≤Σ(λᵢ−1)²。第三批已进一步证明仅λᵢ≥1/4时KL≤2Σ(λᵢ−1)²，并识别为实际矩阵元素平方和。无需特征值上界；论文的具体矩阵估计仍待证。

## 各项目采用状态

| 项目及固定提交 | 实际看到的内容 | 采用判断 |
|---|---|---|
| [StatLean/Stat-Lean](https://github.com/StatLean/Stat-Lean/tree/855b6afb69fead1bef066111732ed44df181040e)，v4.29.1 | `Fano/FanoLowerBound.lean`给出Markov kernel的Fano及minimax风险下界；还有估计到检验的归约 | 多元KL、混合KL、互信息、Fano和估计到检验均已按固定版本移植、编译并公理审计。原库整体未导入；本地GaussianFano已将这些工具接到实际Gaussian矩阵条件 |
| [RemyDegenne/testing-lower-bounds](https://github.com/RemyDegenne/testing-lower-bounds/tree/5d4c306593b8426846ead569bbcbb781e2a965e9)，v4.13.0-rc3，Apache-2.0 | KL、条件KL、检验风险与信息论基础 | 版本较旧；重叠基础优先用现在的mathlib。本次没有确认可直接导入的完整Fano链 |
| [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib/tree/8e6661fe1d5abf0f56ed6b2b8ed0fda37cdc32a1)，v4.33.0，Apache-2.0 | 已阅读Gaussian Lipschitz集中不等式文件 | 保留为集中不等式候选，不为此升级整个项目。log(x²)在0附近不是全局Lipschitz，不能直接替代文件19的Gaussian对数矩引理 |
| [statopia/statlean4](https://github.com/statopia/statlean4/tree/dd2c4bbc72b7c643e62985d77c84755b31aec9f5)，v4.28.0-rc1 | 已阅读Hermite正交性、Gaussian L²完备性等源码 | 与上面的StatLean是不同项目；当前树未找到许可证文件，暂未复制。还需检查依赖、许可证与版本兼容性 |

已移植并编译的StatLean多元定理的实际结论是

\[
D(\mathcal N(0,A)\|\mathcal N(0,B))
=\tfrac12\bigl(\log\det B-\log\det A+\operatorname{tr}(B^{-1}A)-d\bigr),
\quad A,B\succ0.
\]

这与文件09/20所需的工具吻合；论文特征积分、矩阵界、packing所属函数类仍须由本项目证明。

## 第三批实际完成的Fano复用

新增`FanoDefs`、`EstimationToTesting`、`KLMixture`、`MutualInformation`、`FanoLowerBound`，保持原定理的数学前提和结论；修正v4.31.0中ENNReal消去定理名称和非负比较的调用差异。上游全部选定传递依赖已在本项目编译并通过内核公理审计。

本地[GaussianFano](Hurst/GaussianFano.lean)新增参考分布互信息界，构造真实Gaussian候选族，得到由正谱下界、Frobenius误差和目标分离直接推出的检验/minimax下界，并传递到包含候选的整个参数类。完整假设与论文剩余工作见[第三批说明](lean_batch3.md)。

## 不能视为已经解决的支持

- mathlib已有Gaussian过程和Brownian motion，但论文非恒定H的谱模型及离散协方差估计仍需连接。
- mathlib的经典CLT不能直接替代相关三角阵列的短记忆或临界CLT。
- Hermite多项式的定义/导数公式不等于已获得所需的展开、相关矩公式及文件19的高阶矩界。
- 目前还没有在本项目验证可直接替代文件19外部Gaussian矩引理的实现。

实际集成状态与文件摘要记录于[复用清单](verification/lean_reuse_inventory.json)；完整项目验证见[构建日志](verification/build.log)、[公理审计](verification/audit_result.json)和[覆盖清单](verification/coverage.json)。

## 第四批实际采用的mathlib分析基础

在固定v4.31.0中直接复用Trigonometric.Bounds、ImproperIntegrals、L2Space与Measure.Haar.NormedSpace，分别处理实际复指数界、零点/尾部幂积分、复L²的实Hilbert结构及Lebesgue换元。已接到此前的Gaussian Gram构造并导出精确网格协方差；本批没有新增外部依赖。详见[第四批](lean_batch4.md)。

## 第五阶段复用

在固定mathlib版本中实际采用ParametricIntegral的受控积分求导、连续参数积分、实幂/对数渐近、L²范数比较、Gaussian均值与协方差唯一性、矩阵下三角行列式及连续线性映射。由已采用的数据处理不等式双向推出可测左逆下的KL不变性；没有增加外部依赖。完整应用见[第五阶段](lean_batch5.md)。

## 高阶复合偏差的新增复用

继续使用工程固定的mathlib v4.31.0，复用 `Mathlib/Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean` 中的 `iteratedDeriv_comp_eq_sum_orderedFinpartition`（Apache-2.0）。工程自行证明原Hölder类满足其C^m前提，并以有限乘积差界控制公式中每一项；不是将复合Hölder正则性作为前提。整数p仍采用m=⌈p⌉−1。详见[直接证明](proof_notes/smooth_holder_composition.md)。

[第二十五阶段](lean_batch25.md)从mathlib Taylor/矩阵连续性及已验证项目均值方差证明实际等价核和期望偏差首项；适用整数p、额外C^p、固定内部位置与精确最优带宽，q=2真H严格处于截断区间内部。截断反演余项仅需二阶矩。已知非零尺度已接通；CLT、高阶矩及未知尺度精细偏差仍缺。

[第二十六阶段](lean_batch26.md)补齐实际已知尺度估计器的随机线性化和变化样本空间的L¹弱极限传递。复用本地mathlib有界Lipschitz判据；其现有独立同分布CLT不能直接用于本文相关阵列，实际CLT仍待证。

[第二十七阶段](lean_batch27.md)按新顺序补出文件21并建立显式前提的Lean链；已消除q=1未知尺度期望首项的统计输入，q=2及分布传递仍见[条件登记](verification/conditional_results.json)。外部文献引理和内部待形式化引理分别列在[依赖表](verification/dependency_plan.md)。

第二十八阶段当前状态：所列外部及内部支撑前提下的一维下游 Lean 主线已接通，见[汇总](conditional_mainline_summary.md)。仅假设外部文献原引理的更强版本仍未完成，尤其 EXT-MOM→实际 QRawMomentBound 的桥接；最新状态以[条件登记](verification/conditional_results.json)为准。
