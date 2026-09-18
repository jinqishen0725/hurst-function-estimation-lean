# VALIDATION_PROGRESS（供协调 agent 检查；持续更新）

更新:2026-09-18(独立 validation 轮启动)。

## 契约修正记录(2026-09-18 协调检查轮)

协调 agent 复核发现 M1 契约 5 处错误,已全部处理:
1. §2 非负性签名补 `hc : 0 ≤ c`(c<0 时为假;实际模型 c = h(2h−1) > 0)→ 已通知 M1-A
   (M1-A 回复:开工前已独立发现同一问题,两签名带 hc,正性路线改用已落地的
   `RieszOperatorPositivity.laplace_rpow_neg`,剩余缺口 = Schur 三重可积性,自证中)。
2. §3 删除 `exists_positive_sqrt` 的假合取(反例 T=4·Id)→ 已通知 M1-B;
   正确结论:S v_i = √κ_i•v_i、S²=T、自伴、S 非负;各 ∀ 显式包住合取。
3. §3 `mulOperator` 改本质有界 + a.e. 作用引理;`exists_B` 绑定 B = S∘M_ω∘S(同一 S,
   S²=T),矩阵公式为命名合取 → 已通知 M1-B。
4. §4 `hBridge_clm` 加基一致 HS 型假设(紧性不推出谱平方可和,反例 κ_n=1/√(n+1)),
   `Summable (val²)` 升为结论,对角和以 HasSum 陈述 → 已通知 M1-C。
5. §5 降级为草案(非冻结签名);M1-D 派发前先写可检查最小接口。
   Hilbert 基存在改标"内部待证"。
规范已回写(`milestone1_hconst_elimination_math_spec.md` 更正记录 + §2/§3/§4/§5)。

## 当前里程碑

**M1:消除 `hconst` —— 真实等价核谱对象(`B = K^(1/2) W K^(1/2)`,W6/23:A4–A6)与循环积分桥。**
验收 = Lean 落地 B 的构造(自伴、HS、紧、谱枚举平方可和)+ `∑' μ^k = weightedRieszCycleIntegral k`
的桥(或精确列明缺失件)+ 可满足实例(ω = equivalentKernel r)+ build/axiom 日志。

## 验证结论(已完成,全部独立复核)

1. `Session3PremiseAudit.lean` 实跑通过(exit 0);三个不可能性定理公理 = 基础三条:
   - `session3_equivalentKernel_hconst_impossible`:hconst(全域量词)与
     `equivalentKernel_integral r` 矛盾(含 r=1)——**阻断 1 成立**。
   - `session3_fullChain_all_rows_impossible`:FullChainEndpoint 的 `hm : ∀ n, card > 0`
     在 n=0 矛盾——**阻断 2 成立**(FullChainEndpoint.lean:158/318/382 三处)。
2. **阻断 3 成立**(代码核实):`FullChainEndpoint.lean:174` 的 `hE2` 要求未归一化
   `∑∑ rho_ij² ≤ C` 最终一致有界;`featureCorrelation v a a = 1`(GaussianLogRisk.lean:10,
   对角项),故总和 ≥ 活跃点数;可行带宽下 `localWeightActiveSet_card_tendsto_atTop` 发散。
   修复须按 22:W8–W9 的归一化能量 `S^(2ψ-2)·∑∑ rho_ij² = O(1)` 并重审下游(log/clipping/中心化)。
3. **阻断 4 成立**(代码核实):`P3SignedMatching.lean:178/429` 的 `hNegMass → 0` 只覆盖
   负谱渐消;偶次幂不能区分 ±λ。一般带符号极限须按 23:B–D(正/负谱分别排序)另做。
4. 独立复核的其余判定(构建/公理日志可复现;P1 实际谱幂和可用;HS/Parseval/核复合工具
   可复用但"编译 ≠ 适用")全部采纳。

## 状态文档修正

`TRANSITION_session3_2026-09-18.md` 顶部已加更正横幅:撤回"仅余 hPos/收官"结论;
以审查文件与本进度文件为准。审查文件(SESSION3_INDEPENDENT_REVIEW_*.md、
Session3PremiseAudit.lean)原样保留、未覆盖。

## 变更文件(本里程碑)

- 新增:`VALIDATION_PROGRESS.md`(本文件)、`milestone1_hconst_elimination_math_spec.md`(M1 数学契约)。
- 修改:`TRANSITION_session3_2026-09-18.md`(更正横幅)。
- 后续:Agent 产出 `Hurst/UnweightedRieszOperator.lean`(M1-A)、
  `Hurst/PositiveSquareRoot.lean`(M1-B)、`Hurst/EndLevelTraceBridge.lean`(M1-C);
  M1-D(循环积分桥 tr(B^k)=J_k)待三者接口落地后派发。

## 已运行验证

- `lake env lean verification/Session3PremiseAudit.lean` → exit 0(公理仅基础三条)。
- 复核 4 阻断的代码位置(见上)。

## 未消解前提(主线阻断,按修复顺序)

1. **hconst**(阻断 1):M1 进行中。不接受的修法:改量词域/改名/补 Hilbert 基。
2. **hm 全行非空**(阻断 2):把 eventual/安全零填充从
   `actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard` 传播到 FullChainEndpoint
   三处端点(修复方向明确,排在 M1 后)。
3. **hE2 未归一化**(阻断 3):按 W8–W9 重做 P5 能量前提 + 下游估计。
4. **一般带符号极限**(阻断 4):按 23:B–D。
5. 其余内部前提(bias、nondegeneracy、truth-center、unknown-scale 组装)在 2–4 之后。

## 下一步

1. 提交 M1 数学契约(定理签名 + 每个前提在实际模型中的证明方式)。
2. 派发 M1-A(无权 Riesz 算子:A5 正性 Laplace 路线)/M1-B(正平方根 + B + A7)/
   M1-C(hBridge 的 End 级泛化)三路并行(文件互斥)。
3. M1-A/B/C 验收后派 M1-D(循环积分桥),完成 M1 验收(实例 + build/axiom 日志)。
