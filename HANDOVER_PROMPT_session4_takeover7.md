# Session-4 接管任务书(takeover7):标量率实例化(R/hcut/hEnv)→ γ = f t 可行实例 → 数据前提分类定稿 → 收尾

## 0. 环境与对象

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `ed69bf7`,提交链见 §1)。
- 里程碑状态:takeover6 已完成并落地(commit `65aa208` formal / `ed69bf7` docs;
  检查点 `verification/checkpoints/2026-10-05-1827-mainline-blockers234-endpoint/`)。
  **阻断 1/2/3/4 全部关闭,主端点已在消解前提上组装**:
  `Hurst/FullChainGeneralSigned.lean:349` `actualQ1_knownScaleH_fullChain_generalSigned`
  (truth-centered:`2 n^{ψ(1−γ)} log n (Ĥ_n − f t) ⇒ −Q`,Q 为构造的 signed 加权
  Riesz 二阶混沌律)。**hm/hE2/hNegMass/hlam/hQ/偶次 hPow/hW0 已从主线全部消失,
  不得回退或重开;hconst 线条件文件照旧不碰。**
- 本轮里程碑:任务 1(标量率实例化)→ 任务 2(γ = f t 可行实例)→
  任务 3(数据前提分类定稿)→ 任务 4(backlog/TRANSITION 收尾)。顺序执行。
- 当前状态一句话:端点只剩"标量率前提未在 Lean 中实例化 + 三个真数据前提
  (hane/hband/hBias)";聚合验收基线 = 全量 `lake build Hurst` 9213 jobs 绿、
  AxiomAudit 2541 条全 ⊆ {propext, Classical.choice, Quot.sound}、零 sorry。
  工作区应干净(仅协调员的未跟踪改动 `ZCODE_VALIDATION_MONITOR.md`,勿碰)。

## 1. 已落地快照(takeover6 全景;全部 exit=0、零 sorry、公理 ⊆ 三公理)

- 阻断 2:`hm` 移出 FullChainEndpoint 三处端点;Layer 1/seam 走
  `CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard`。
- 阻断 3:归一化能量五新件 `Hurst/Normalized{HermiteEnergy,ActualEnergy,
  ActualRemainder,LogVariance,LogProjection}.lean`;矛盾定理入档
  `verification/Session4Blocker3Audit.lean`(`session4_unnormalized_hE2_impossible`,
  新引理 `featureCorrelation_self`)。
- 阻断 4:六新件 `Hurst/{IntervalL2Basis,WeightedRieszSpectrumClosed,
  GeneralSignedPowerMatching,SignedInterleavedLaw,SignedPowerLimit,
  ActualQ1SignedClosed}.lean`(内部构造 Hilbert 基;三前提闭谱;
  Weierstrass 连续测试 + 分符号排序 + 无逐行前提系数匹配;置换恒等分布;
  构造二阶混沌极限;可行带宽二次端点)。
- 端点组装:`P5LogHLayers` Layer 1'(`actualQ1_logStatistic_tendsto_secondChaos_doubleSum`,
  double-sum 余项形式)+ `P5SeamClosed` 通用 seam 核心
  (`logStatistic_knownScaleH_seam_of_logLimit`;旧 seam 改薄包装,签名不变)+
  `Hurst/FullChainGeneralSigned.lean`(`gs_fourthEnergy_eq:117` 谱权四阶能量 ≡
  `q1ActiveWeightedFourthEnergy`;`gs_fourthEnergy_tendsto_zero:186`;
  `gs_logProjection_L1_tendsto_instantiated:249` 归一化 hJoin;主端点 :349)。
  **消解表(先于形式化写就)在该文件头 §"How the new premises resolve"**。
- 文档回写:VALIDATION_PROGRESS 置顶块(2026-10-05)、TRANSITION §0 快照(2026-10-05)。
- 来源注记:2026-09-26 并行 session 的未提交产物已经本轮全量审计后落定
  (其 `GeneralSignedPowerMatching.lean` 从未编译通过,由 takeover6 修复;详见
  `COORDINATION_2026-09-26.md` 与 VALIDATION_PROGRESS 置顶块前置说明)。

## 2. 必读文档与顺序

1. `VALIDATION_PROGRESS.md` 置顶块(2026-10-05):takeover6 落地表 + 已知缺口登记
   (本任务书的任务 1/2 就是其中"标量率 R 实例化未接线"一条)。
2. `Hurst/FullChainGeneralSigned.lean` 全文,尤其文件头消解表与 :349 端点的前提列:
   hgrid(:356)、hane(:357)、hR(:360)、hcut(:361)、hEnv(:365)、hband(:370)、
   hE5(:378)、hBias(:380)。
3. `TRANSITION_session4_2026-09-21.md` §0(2026-10-05 快照)与 §3/§4(纪律与流程)。
4. 率引理素材(逐行核对,行号已验证):
   - `Hurst/FirstScaleLongRates.lean:11` `mesh_log_power_rpow_tendsto`
     (`(1 + log (2n))^k * n^r → 0`,r < 0;log 因子全靠它吸收);
   - `Hurst/LocalWeightSupport.lean:10` `localWeightActiveSet_card`
     (`card ≤ 3 * (n δ)`,需 `0 < δ` 与 `1 ≤ n δ`;配合
     `OptimalActiveRowDensity.lean:139` `localWeightActiveSet_card_tendsto_atTop`);
   - `Hurst/GridCorrelationDecay.lean:58` `gridCovarianceError` 显式式
     `C * (1 + log (2n)) * (n^{-1} + n^{2b-2})`;
   - `Hurst/GridErrorRate.lean:105/210`(`S^{ψ-1}` 形先例,证明风格可抄);
   - hE5 消解先例:`Hurst/FullChainEndpoint.lean:432` `have hE5 : (1 - f t) * (2 - 2 * f t)
     < f t * 1` 的纯算术块(γ = f t 时 ψ² < f t 由 hlong 即得)。
5. E5/hBias 方向的现成机械(任务 3 用):`Hurst/E5RateLink.lean:123`
   `correlationEnergy_rate`、:300 `e5_fluctuation_rate_of_window`
   (L1 波动率 ≤ F·n^{-γ} 的窗口定理);旧线消费链
   `E5ChainInstantiation.e5_fluctuation_at_chain` → `P5TruthCenter` drift。

## 3. 任务序列(按序;小步优先,每步独立落地)

任务 1 = 标量率实例化(新文件,建议 `Hurst/FeasibleRates.lean`):
在可行带宽 `δ n = n^{-γ}` 下,取 `R n := ⌊(n : ℝ)^β⌋`(β 待定窗口),Lean 证明
(a) hR:`R → ∞`(用 `Real.tendsto_nat_floor` 复合 `tendsto_rpow_atTop`);
(b) hcut:`S^{2ψ−2} · card · (2R+1) → 0`,ψ = 2 − 2 f t。数学(已手推,直接落地):
`card ≤ 3S` eventual(LocalWeightSupport:10),故上式 ≤ `3 n^{(1−γ)(2ψ−1)} (2⌊n^β⌋+1)`,
指数 `(1−γ)(2ψ−1) + β < 0 ⟺ β < (1−γ)(1−2ψ) = (1−γ)(4 f t − 3) > 0`
(hlong : 3/4 < f t 保证为正;窗口非空);+1 项指数 (1−γ)(2ψ−1) < 0 自消;
(c) hEnv(对**任意固定** Ccov ≥ 0、Ctail ≥ 0、L > 0;各项对常数线性,逐项 squeeze,
不存在两存在见证的耦合):包络五项——
  (i) `D = 2L(1+M)δ = 2L(1+M)n^{-γ}`,`E := D log n → 0`(log·n^{-γ},用
      mesh_log_power_rpow_tendsto k=1),`e^E · E → 0`(连续性),故
      `18 Ctail D (1 + e^E E) → 0`、`9 e^E E → 0`、`(3/2) D → 0`;
  (ii) `16/(R+1) → 0`(由 hR);
  (iii) `4 (2S)^ψ · gridCovarianceError b Ccov n = 4·2^ψ·n^{(1−γ)ψ}·Ccov(1+log 2n)
      (n^{-1} + n^{2b−2})`:n^{-1} 项指数 (1−γ)ψ−1 < 0 恒成立;n^{2b−2} 项指数
      `(1−γ)ψ + 2b − 2 < 0 ⟺ hgrid`(恰是端点已有前提);log 因子由
      mesh_log_power_rpow_tendsto 吸收。
落地后:主端点新变体(或直接补一版"hR/hcut/hEnv 全消解"的包装定理),并把
VALIDATION_PROGRESS 的已知缺口第一条销账。**先数学后 Lean;若与消解表出入,
以 Lean 实际证出者为准并回写消解表。**
任务 2 = γ = f t 可行实例变体(镜像旧 `_feasible`,FullChainEndpoint:381 先例):
hE5 由 hlong 纯算术消解(抄 :432 的块);hgrid 在 γ = f t 时化为数据侧 b-带条件
`(1 − f t)^2 < 1 − b`(等价 b > 1 − (1−f t)^2,可满足);β-窗口化为
`β < (1 − f t)(4 f t − 3)`。产出
`actualQ1_knownScaleH_fullChain_generalSigned_feasible`:前提进一步缩为
模型窗口 + b-带 + hane + β + 中心带/E5 偏差数据。
任务 3 = 数据前提分类定稿(诚实条款的核心):
对 hane / hband(cσ, d)/ hBias(E5 偏差包络)逐一给出"数据前提 vs 可消解"的
定稿分类,写入 VALIDATION_PROGRESS(§1 表格式)。已知背景:
- hBias 方向有机械(E5RateLink:300 的 L1 波动率窗口定理、E5ChainInstantiation
  消费链),但旧线四轮均保持 explicit;若动手消解,按新里程碑立项,不得在
  本轮偷偷以弱化结论换取"绿"。
- hband 是中心校准(cσ 的统计选择,file-22-W9 口径);hane 是特征行非退化
  (M1 分类即数据前提)。
分类定稿本身即是交付物;不强制消解。
任务 4(余量)= backlog.md 清理与 TRANSITION 收尾(原任务书任务 5 遗留)。

## 4. 硬性纪律(违反须返工;与前几轮相同)

- 默认禁用 subagent:全部形式化亲自完成(2026-09-26 的并行授权已随该轮结束
  过期;仅当用户当轮明确重新授权时例外)。
- 落地前偏差自检:(a) 等式/不等式方向;(b) 前提真实消费,文档不超签名;
  (c) 新前提全量词域可满足(反例清单纪律)。
- 编译证据:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`;
  验收 ≠ 编译绿:公理 ⊆ 三公理 + 检查点四件套(源快照 + compile.log +
  axioms.log + sha256.txt,目录内裸名);/tmp 做公理审计前先 `lake build` 刷新
  olean;检查点时间戳用 `date` 实际输出;聚合时写 `verification/build.log`
  并追加 `verification/AxiomAudit.lean`。
- land-then-follow-through:新鲜编译 → 检查点 → git commit → 增量
  `lake build Hurst` → 回写 VALIDATION_PROGRESS 与 TRANSITION。
- 小步优先;同一声明卡 >2 次同一错误,贴 trace_state 原文求助。
- 不碰 `ZCODE_VALIDATION_MONITOR.md`;文档编辑用 python 字符串手术。

## 5. v4.31 雷区(累积版在 VALIDATION_PROGRESS 置顶块;takeover6 新增批摘录)

- `neg_pow` 不可进 `simp only`(RHS 含 `(-1)^k` 自匹配 → 实例合成假性递归爆栈,
  报 `HasDistribNeg ℝ` maximum recursion depth):用 `rw [neg_pow]` 逐点改写 +
  `funext` 具名逐点引理。
- `HasSum.even_add_odd` 点记法(`he.even_add_odd ho`)会触发高阶统一 whnf
  超时(2M 心跳也挂):显式实例化 `(f := …)` 后再应用。
- `Filter.Tendsto.congr'` 的参数是 `EventuallyEq`(f₁ =ᶠ f₂),方向要留心
  (`h.congr' heq` 要求 heq : 目标函数 =ᶠ 已收敛函数,反向用 `.symm`/
  `.mono fun n h => h.symm`)。
- 位置参数内嵌 `by` 块解析易碎:先 `have` 具名再传参。
- `Finset.sum_mul` 方向:双和提常数用 `simp only [← Finset.mul_sum]`
  (`rw [Finset.sum_mul]` 会匹配错侧)。
- `Real.rpow_add` 合并 `x^a * x^1` 时先 `rw [Real.rpow_one]` 或反向展开
  (`(x ^ a) * x` 不自动匹配 `x ^ a * x ^ b`)。
- `filter_upwards` 不能直接消耗 `False` 目标:先 `Eventually.exists` 取见证。
- 其余(fun x => 逗号、HasSum.congr_fun、abel in L2、Orthonormal 字段、
  opNorm 链小上下文提取等)见置顶块累积表。

## 6. 汇报要求(诚实条款)

landed / not-landed 分列;conditional / unconditional 分列;任务 1 的新率定理
须附"实际模型中如何消解"的指数算术(先数学后 Lean,回写消解表);编译日志
路径 + 真实 exit code + 公理审计输出原文;已知缺口如实登记;hane/hband/hBias
在任务 3 定稿前,不得宣称"端点全实例化/统计闭环"。
