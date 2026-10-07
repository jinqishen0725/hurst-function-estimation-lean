# INTEGRATION.md — E5BiasExpansion 集成清单(第二 agent,并行轮)

状态:`Hurst/E5BiasExpansion.lean`(1030 行)`lake env lean` exit=0、
零 sorry、文件内联 `#print axioms` 17 条全部 ⊆ {propext, Classical.choice, Quot.sound}
(lean.log 原文)。本目录四件套:源快照 + lean.log + sha256.txt(裸名)。
**未做任何 git 操作;未 import 进任何聚合目标**(集成由主线收尾统一做)。

## 1. 挂线方式

- 在 `Hurst.lean`(或主线惯用的聚合入口)追加 `import Hurst.E5BiasExpansion`;
  本文件 import 的六个模块(`P5L1Joining/VaryingIncrement/FirstStrideGrid/
  HolderTaylor/ActiveSetReindex/E5ChainInstantiation`)均已在聚合树内,无新依赖。
- 聚合 `lake build Hurst` 后把下列 17 行追加进 `verification/AxiomAudit.lean`
  (即文件尾已有的 17 条 `#print axioms`,全部三公理、无 sorryAx)。

## 2. 公开定理清单(全部命名空间 Hurst)

任务 A(截断期望,全抽象):
- `abs_log_one_add_le_two_mul` — |log(1+x)| ≤ 2|x|(|x| ≤ 1/2)
- `abs_add_le` — 三角不等式 a+b 形(abs_sub+abs_neg 手拼;仓内无裸 abs_add)
- `truncExpectation_le_fluctuation` —
  |E p5Trunc01(X) − E X| ≤ E|X − E X|(E X ∈ Icc 0 1)

任务 B(增量范数对数展开,Harmonizable 侧):
- `varyingIncrement_norm_sq_error` —
  |‖varying‖² − 1| ≤ 3·C·K·ℓ^(1−b)(前提 |k−h| ≤ K·ℓ、C·K·ℓ^(1−b) ≤ 1)
- `varyingIncrement_logNormSq_error` —
  |log ‖varying‖²| ≤ 10·C·K·ℓ^(1−b)(smallness ≤ 1/2)
- `gridStrideFirstActual_logNormSq_error` —
  |log ‖gridStrideFirstActual n 1 (midpointSampleHurst) i‖²|
  ≤ C'·n^{−(1−b)},C' = 10·D·(1+M),D 来自 hurstHolder_uniform_lower_derivative_lipschitz

任务 C(Hölder 权收缩):
- `holderWeightContraction` — 抽象:|∑w_j f(x_j) − f t| ≤ (W·M/⌊p⌋!)·δ^p
  (显式前提 hsum/hmom/hW/hgeo;主线中间件不重复实现)
- `localPolynomialWeights_abs_sum_active` — 活动重索引下全变差恒等
- `holderWeightContraction_localPolynomialWeights_of_stable` —
  稳定性输入版(Cstab + 矩条件 ⇒ 收缩)
- `exists_holderWeightContraction_localPolynomialWeights` —
  ∃N₀>0, ∃Cstab>0 包装(localPolynomialWeights_uniform_stability 派发前提)

接口/恒等式(E5ChainInstantiation ↔ P5LogHLayers):
- `unitStatWeight_eq_localPolynomialWeight` — ŵ_j = w_{idx j}(S=n·δ)
- `chainLogStatistic_eq_rpow_smul` —
  chainLogStatistic = S^{2−2ft} · p5KnownScaleLogStatistic(权重成比例+组合向量同)
- `chainCalibratedStatistic_eq` —
  chainCalibratedStatistic = S^{2−2ft}·p5KnownScaleHtilde(cσ/S^{2−2ft})

任务 D(组装):
- `p5KnownScaleHtilde_expectation_eq` —
  E Ĥtilde = ∑ŵ_j H_j + (cσ − c₀ − ∑ŵ_j L_j)/(2 log n)(精确恒等式;hw1 显式前提)
- `p5KnownScaleHtilde_drift_bound` —
  |E Ĥtilde − f t| ≤ D + (|cσ−c₀| + W·E)/(2 log n)
- `knownScaleEstimator_bias_envelope` — 抽象包络 |E p5Trunc01 X − θ₀| ≤ F + D
- `knownScaleEstimator_bias_envelope_grid` — 最终条件包络:
  |E p5KnownScaleEstimator − f t| ≤ (F + Cst + Clog·W/2)·n^{−γ},
  前提含 hw1/hWabs/hcontr/hlog/hcσ(cσ = gaussianLogSquareMean)/
  hbandc(E Htilde ∈ Icc 0 1)/hfluct(E5RateLink 形)/hγ(γ ≤ 1−b)/hδp(δ^p ≤ n^{−γ})/n ≥ 3

## 3. 建议追加的 AxiomAudit 行

文件尾 17 条 `#print axioms Hurst.*` 原样追加(见 lean.log;
全部 `[propext, Classical.choice, Quot.sound]`)。

## 4. 诚实登记(重要;不得粉饰)

1. **n^{−(2−b)} 蓝图算术错误**:uniform_remainder 的前提形状是
   `|k−h| ≤ B·ℓ`,Hölder-Lipschitz 轮廓只给 |k−h| = O(ℓ)(B = O(1)),
   结论只能是 C·B·ℓ^{1−b} = O(n^{−(1−b)}),**不是** n^{−(2−b)}。
   全部定理按诚实率 n^{−(1−b)} 陈述。
2. **γ-窗口真实缺口**:诚实率下 ε-项 = W·Clog·n^{−(1−b)}/(2 log n),
   拟合 n^{−γ} 预算当且仅当 γ ≤ 1−b。端点 γ = f t ∈ (3/4,1) 且
   b > f t(可行实例 b-带)⟹ 1−b < 1−f t < f t = γ,**窗口不成立**——
   `knownScaleEstimator_bias_envelope_grid` 在 γ = f t 处**不能**消解端点 hBias。
   补缺口需二阶增量展开(≥ n^{−(2−b)} 率)或谱端等价论证,均不在仓内。
3. **任务书雷区条目的核验结果**(任务书 §4):γ = f t、c := 1−γ 联立
   2γ ≤ c(4ft−3) 即 2ft ≤ (1−ft)(4ft−3);ft ∈ (3/4, 5/6) 时
   RHS−LHS = (1−ft)(4ft−3)−2ft = −6ft²+7ft−3,判别式 49−72 < 0,**恒负**——
   该方向不可解(需要 ft ≥ 5/6 或另选 c);这是任务书预判"若不恒真如实登记"
   的确认:e5_fluctuation_rate_of_window 的 hmesh/hwin 在 γ = f t、c = 1−γ 下
   **联立不可满足**,与第 2 条同源(flutuation 侧同样卡在率窗口)。
4. **cσ/c₀ 常数**:c₀ = gaussianLogSquareMean(GaussianLog.lean:82,
   E log χ²(1));cσ := c₀ 精确消去 1/log n 常数项;任何 cσ ≠ c₀ 的常数偏移
   只以 1/log n 衰减,慢于一切多项式率(包络定理按 |cσ−c₀| 显式保留该项)。
5. **与蓝图的其余偏差**:(a) 抽象截断引理用截断几何五分情形而非
   Lipschitz×eq_self 两行(lip 一行版不够证,诚实);(b) hane 在
   identity/drift_bound/envelope_grid 中是行非退化前提(与端点同形);
   (c) hw1/hWabs/hcontr/hlog/hfluct/hbandc 均为显式前提,等主线中间件
   (∑w=1、收缩常数的 actualQ1 实例化)落地后拼接。

## 5. 拼接提示(主线)

- 主线若产出 `∑ j, (S⁻¹·u_j) = 1`(actualQ1ChainWeight 版),直接替换
  `hw1` 前提;`exists_holderWeightContraction_localPolynomialWeights` 已给出
  localPolynomialWeights 侧的收缩常数(Cstab·M/⌊p⌋!·δ^p,稳定性窗口
  N₀ ≤ n·δ、δ ≤ 1/2),与 `hcontr`(f(grid(idx j)) 版)经
  `unitStatWeight_eq_localPolynomialWeight` 换底。
- `chainCalibratedStatistic_eq` 把 E5RateLink:300 的统计量与
  p5KnownScaleHtilde 接上(差一个 S^{2−2ft} 因子与中心重标度),
  hfluct 前提即由 e5_fluctuation_rate_of_window 经此换算(注意第 4.3 条
  率窗口限制)。
