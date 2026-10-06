# Session-4 接管任务书(takeover8-parallel,第二 agent):hBias 里程碑第一块——截断期望引理 + 增量范数对数展开 + Hölder 权收缩 + 组装蓝图

## 0. 环境与并行协作协议(先读,最重要)

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `4bce44f`,任务书 commit `554580b`)。
- **你与主线 agent(takeover8,执行 hane/hband 消解)在同一工作区并行工作。**
  主线任务书 = `HANDOVER_PROMPT_session4_takeover8.md`(先通读其 §0–§2 以了解
  全局,但你只做本文件的任务)。为避免冲突,遵守以下硬边界:
  1. **你的可写面 = 恰好一个新文件 `Hurst/E5BiasExpansion.lean`**、你自己的
     检查点目录 `verification/checkpoints/<date-time>-E5BiasExpansion/`、
     以及 `/tmp` 下的日志。**其余一切只读**——尤其不碰
     `Hurst.lean`、`Hurst/FeasibleRates.lean`、`Hurst/FullChainGeneralSigned.lean`、
     `Hurst/P5*.lean`、`Hurst/CenterBandDischarge.lean`(主线 agent 的新件)、
     `VALIDATION_PROGRESS.md`、`TRANSITION_*`、`verification/AxiomAudit.lean`、
     `verification/build.log`、`ZCODE_VALIDATION_MONITOR.md`。
  2. **禁用 `lake build`**(与主线的聚合构建抢 .lake 锁):你的验证一律
     `lake env lean Hurst/E5BiasExpansion.lean > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`
     (你的 import 全部是已构建模块,olean 现成)。公理审计用文件内联
     `#print axioms`,不另建 /tmp 审计文件。
  3. **禁用一切 git 写操作**(不 add/commit/stash/branch):集成(挂 import、
     聚合 build、AxiomAudit 追加、commit、文档回写)由主线 agent 收尾时统一做;
     若你先完成而主线仍在跑,把"集成清单"(文件内公开定理逐个列出 + 建议追加的
     AxiomAudit 行)写进你检查点目录的 `INTEGRATION.md`。
  4. 若你的引理需要主线正在产出的中间件(如 ∑w=1):**把该事实作为显式前提
     (hsum)陈述你的引理,不要自己另证一份**(避免分叉);集成时由主线拼接。
- 背景一句话:端点 `Hurst/FeasibleRates.lean:453` 的最后三个数据前提中,
  主线并行攻 hane(:460)与 hband(:465);你攻 **hBias(:474)的第一块**。
  hBias 要的是率 `|E Ĥ_n − f t| ≤ C·n^{−γ}`,而一阶展开只给 `o(1)`——
  这个率差就是 E5 里程碑的实质内容,你的交付是把这个差距拆成可形式化的
  引理并做掉其中独立的三块。

## 1. 数学蓝图(手推草图;待 Lean 验证,符号以实际证出者为准)

记 `Ĝ_unit = p5KnownScaleLogStatistic`(单位权 `w = S⁻¹·u`),
`Htilde = (cσ − Ĝ_unit)/(2 log n)`,`Ĥ = p5Trunc01 ∘ Htilde`,
`E` = featureGaussian 期望。分解:
`E Ĥ − f t = [E Htilde − f t] + [E(p5Trunc01(Htilde)) − E Htilde]`。

**第一项(中心选择)**:由 `gaussianLogStatistic_expectation`
(`Hurst/GaussianLog.lean:153`)与 FirstStrideGrid:24 恒等式
(组合向量范数 = `(1/n)^{H_j}·‖增量_j‖`,frozen 增量范数 = 1
`VaryingIncrement.lean:26`):
`E Ĝ_unit = ∑ w_j(−2 H_j log n + log‖增量_j‖² + gaussianLogSquareMean)`
`= −2(∑ w_j H_j)·log n + c₀ + 误差`,其中 `c₀ := gaussianLogSquareMean`
(在 ∑w=1 下)。于是
`E Htilde − f t = −(∑ w_j H_j − f t) + (cσ − c₀ + 误差项)/(2 log n)`;
**取 `cσ := c₀` 消掉 1/log n 主项**,剩
`= O(δ^p) + O(n^{−(2−b)}/log n) + O(|∑w−1|·c₀/log n)`。
在 `p ≥ 1`(hp)与 `γ ≤ 2 − b`(由 hgrid 可得,需验证)下,整体 `O(n^{−γ})`。

**第二项(截断损失)**:对任意实值随机变量 X 与任意 `x₀ ∈ [0,1]`:
`|p5Trunc01 x − x| = |p5Trunc01 x − p5Trunc01 x₀| ≤ |x − x₀|`
(`p5Trunc01_lipschitz`,P5L1Joining.lean:108 + `p5Trunc01_eq_self`,
P5LogHLayers.lean:69)。取 `x₀ = E X`(在带内时)得
`|E p5Trunc01(X) − E X| ≤ E|X − E X|`。
而 `E|Htilde − E Htilde|` 正是 `e5_fluctuation_rate_of_window`
(`Hurst/E5RateLink.lean:300`)给出的 `≤ F·n^{−γ}` 形状
(注意核对其统计量 `chainCalibratedStatistic` =
`(cσ − chainLogStatistic)/(2 log n)`,`Hurst/E5ChainInstantiation.lean:201`,
与 `p5KnownScaleHtilde` 同形——若两者不完全 defeq,补一个恒等/改写小引理)。

## 2. 任务序列(小步优先;每块独立成定理)

任务 A(全抽象,无耦合):`E5BiasExpansion` 截断期望引理——
`theorem truncExpectation_le_fluctuation {Ω} [MeasurableSpace Ω] {μ} [IsProbabilityMeasure μ]`
对可积 X、`E X ∈ Icc 0 1`:`|∫ p5Trunc01 ∘ X ∂μ − ∫ X ∂μ| ≤ ∫ |X − ∫ X ∂μ| ∂μ`。
(点态不等式 + 积分;无需任何 Hurst 结构。)
任务 B(Harmonizable 侧,只读复用):增量范数对数展开——
`‖varying增量_j‖² = 1 + ε_{j,n}`,`|ε_{j,n}| ≤ C·n^{−(2−b)}`:
用 `VaryingIncrement.lean:37` uniform_remainder(B = |k−h| 经
`hurstHolder_uniform_lower_derivative_lipschitz` HolderRegularity:54 或
`harmonizableFeature_uniform_parameter_lipschitz` SpectralMajorant:263 控制
到 O(1/n),ℓ = 1/n)+ frozen norm = 1(:26);再
`log‖·‖² = O(ε)`(子引理:`|x| ≤ 1/2 ⇒ |log(1+x)| ≤ 2|x|`,
可用凸性/中值自证,不要硬 simp)。
任务 C(权侧,带显式前提 hsum):Hölder 权收缩——
在 `hsum : ∑ w_j = 1` 与活跃窗几何(窗内 |x_j − t| ≤ C·δ,自行 grep
ActiveWindow*/LocalWeightSupport 现成引理;重加索引用
`localPolynomialWeights_sum_active`,`Hurst/ActiveSetReindex.lean:26`)下:
`|∑ w_j H_j − f t| ≤ M'·δ^p`(H_j = f 在格点的值,f ∈ hurstHolderClass p M)。
任务 D(组装蓝图,不强制全形式化):把 A+B+C 拼成
`E Ĥ_n − f t = O(n^{−γ})` 的条件定理(以 hsum/窗口/hgrid 为前提),或若
时间不够,写成 `INTEGRATION.md` 蓝图 + 已形式化块的精确接口清单。
**诚实条款:任何一步被证伪(尤其 `γ ≤ 2−b` 的方向或 c₀ 的常数),立即登记
并改以证出的形状陈述;不得弱化端点的 hBias 定义。**

## 3. 验收与汇报

- 每块:`lake env lean` exit=0、文件内联 `#print axioms` 全 ⊆
  {propext, Classical.choice, Quot.sound}、零 sorry。
- 检查点:你的目录内(源快照 + lean.log + sha256.txt 裸名;时间戳用 `date`)。
- 汇报(写在你的最终输出里,不写共享文档):landed / not-landed 分块;
  每个定理的签名原文;与蓝图的偏差;cσ/c₀/常数的显式值;
  "集成清单"(若主线未及集成)。不 commit。

## 4. 纪律与雷区(与主线任务书 §4/§5 相同,外加)

- 全部形式化亲自完成,不用 subagent;不碰共享文件(§0 边界)。
- 雷区补充:`Real.log(1+x)` 型界不要交给 simp(先手证子引理);
  期望与截断交换时方向自检(`|E f(X) − E X| ≤ E|f(X) − X|` 用
  `abs_sub_comm`/Jensen 风格逐点,勿引错方向);
  `E5RateLink:300` 的前提 `hmesh : n^c ≤ n·δ` 在 δ = n^{−γ} 下即 `c ≤ 1−γ`,
  注意与 hwin `2γ ≤ c(4ft−3)` 联立可解(`c := 1−γ` 需 `2γ ≤ (1−γ)(4ft−3)`,
  γ = f t 时即 `2ft ≤ (1−ft)(4ft−3)`,ft > 3/4 下验证是否恒真——若不恒真,
  这是蓝图的真实约束,如实登记);`Tendsto.congr'` 方向以 takeover7 勘误为准。
- 其余雷区见 `VALIDATION_PROGRESS.md` 置顶块累积表(只读)。
