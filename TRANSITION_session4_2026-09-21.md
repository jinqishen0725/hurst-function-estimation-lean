# Session 4 交接:独立验证轮的 M1 执行状态(take-over 文档)

更新:2026-09-21 17:02 PDT。HEAD `7814f84`。项目:
`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`。
本文件供接管 agent 使用;权威过程记录见 [VALIDATION_PROGRESS.md](VALIDATION_PROGRESS.md)
(逐检查点、逐契约修正、含日志路径与退出码)。

## 1. 背景与使命(必读)

上一轮(Session-3)宣称的"收官"被独立复核否决
([SESSION3_INDEPENDENT_REVIEW_2026-09-18.md](SESSION3_INDEPENDENT_REVIEW_2026-09-18.md),
其 Lean 证明在 [verification/Session3PremiseAudit.lean](verification/Session3PremiseAudit.lean),
`lake env lean` 实跑 exit 0)。四个已核实阻断:

1. **hconst 不可满足**(Lean 证明):全域量词的"ω 在 [-1,1] 指示下为常数"强迫区间内
   ω=0,与 `equivalentKernel_integral r = 1` 矛盾(含 r=1)——所有下游
   (`CapstoneV3Closed`、`rieszSpectrumVal_hGen`、P2 谱构造)不能实例化到实际等价核。
   根因:谱算子被定义为带权核 `ω(x)c|x−y|^{-ψ}`(W K),一般非自伴;hconst 是掩盖
   非对称性的捷径假设。**修复路线 = 22:W6 / 23:A4–A6 的 B = K^{1/2} W K^{1/2}**。
2. **FullChainEndpoint 的 `hm : ∀ n, card > 0`** 在 n=0 矛盾(Lean 证明);
   eventual/零填充修法已有先例(`..._signed_eventualCard`),未传播到端点层。
3. **P5/FullChainEndpoint 的 hE2**(未归一化 ∑∑ρ²≤C)不可满足:对角 ρ=1,
   活跃点数发散;须按 22:W8–W9 归一化能量重做并重审下游。
4. **P3SignedMatching 的 hNegMass→0** 只覆盖负谱渐消;一般带符号极限须 23:B–D。

**修复顺序(用户指定):1→2→3→4,最后端点组装。** 当前处于阻断 1 的里程碑 M1。

## 2. M1(消除 hconst)记分板 @ 2026-09-21 17:02

| 件 | 文件 | 状态 | 提交 |
|---|---|---|---|
| M1 契约 | `milestone1_hconst_elimination_math_spec.md` | **权威契约**(冻结签名+前提模型消解表+更正记录 1–7;§5 = D2 压缩路线) | be201e8…8a3db4e |
| M1-A 无权算子 | `Hurst/UnweightedRieszOperator.lean`(696 行,**未提交**) | ⚠️ 中间态:exit=1,6 错(首错 488:11 `measure_mono_null` 未知名;489 no-goals;505 类型失配)。**13:45 曾全绿**(36 声明含 hc 版正性 `inner_TOp_unweightedRiesz_nonneg`/`exists_nonneg_eigenfamily`,证据降级见 §4)——收敛这 6 错即完成 | — |
| M1-B 平方根/B | `Hurst/PositiveSquareRoot.lean`(878 行,**未提交**) | ⚠️ 中间态:exit=1,**仅 2 错**(764 whnf 800k 超时;822 unsolved)。乘法算子层(mulOperator+双前提 hm/hess+action+范数+equivalentKernel 适用性)与 specPair 可和层已绿;`exists_positive_sqrt`/B=S∘M∘S 绑定/A7 待收尾 | — |
| M1-C End 级迹桥 | `Hurst/EndLevelTraceBridge.lean`(1291 行) | ✅ **全绿落地**:`exists_diag_enumeration_clm`、`hBridge_clm`(hTHS 假设+Summable val² 结论+HasSum)、`hBridge_clm_tsum`、`summable_kappaSq_of_matrixSq`(M1-D 消费件);公理干净;检查点 `verification/checkpoints/2026-09-18-1520-M1C/` | fcc2822 |
| A8 有限迹恒等式 | `Hurst/FiniteMatrixTraceCycle.lean` | ✅ **全绿落地**:`trace_pow_eq_cycleSum`/`trace_Bm_eq_cycleSum`(κ≥0)/`trace_WKm_eq_cycleSum`;`Fin (k+1)` 编码 k≥1(声明偏差,k=0 字面为假);检查点 `2026-09-18-1714-A8/` | e05b356 |
| M1-D1(非承重) | `Hurst/TracePairCycle.lean` | ✅ `tracePair_cyclic`(**角色降级**:S=√K 非 HS,cyclicity 移 S 不合法;保留为可复用工具);检查点 `2026-09-18-1500-M1D1/` | 81405a4 |
| M1-D2 压缩胶水 | `Hurst/EquivalentKernelSpectrum.lean`(未建) | ⏳ **未开始**——契约在规范 §5(A8–A9 路线:ι 可数化→A8 恒等式→三项收敛→加权认同→组装+equivalentKernel r 实例);依赖 A/B 落地 | — |

中断原因:M1-A/B 两个 agent 于 09-18 19:27 触发 5 小时配额,文件停在中间态;
接管者第一步 = 把 A(6 错)、B(2 错)收敛到绿(契约签名在规范 §2/§3,含全部更正:
hc、双前提 hm+hess、删假合取、B 绑定定义式)。

## 3. 硬性流程纪律(协调 agent 多轮纠偏的沉淀,违反必返工)

1. **检查点协议**:通过 = 专属目录 `verification/checkpoints/<日期时刻>-<件>/` 绑定
   {源码快照 .lean, 完整日志 .log(内嵌真实 `exit=`), sha256.txt(目录内裸名)}。
   禁止 /tmp 可预测路径(曾被覆盖,事故存档 `2026-09-18-1345-incident/`)。
2. **编译证据**:`lake env lean F > LOG 2>&1; echo "exit=$?" >> LOG`——全量重定向,
   真实退出码。**禁止** `| head` 管道(其 `$?` 是 head 的;截断日志)。
3. **先数学后 Lean**:新块先写进规范(签名+前提在实际模型中的证明方式),再形式化;
   规范是可证伪初稿,偏差声明式回写。**禁止把待证内部条件包装成"普通假设"完成主线**。
4. **小块先行**:先落可编译小块并报最小编译检查点;单声明卡壳 >2 次上报 trace_state。
5. 每个前提在契约 §1 表格有"实际模型中如何消解"一栏(本轮核心教训)。
6. 验收 ≠ 编译绿:需 axiom 检查(⊆ propext/Classical.choice/Quot.sound)+
   可满足实例(equivalentKernel r)+ 全量 build 日志。
7. 性能:逐声明计时定位慢项(`trace.profiler`);局部 maxHeartbeats 须注释;
   禁止全文件预算掩盖。
8. 语言纪律:hg 类"内部可消解前提"≠ hconst 类"不可满足前提",不得混用;
   编译通过 ≠ 目标完成。

## 4. 历史检查点与证据等级(诚实记录)

- **13:45 检查点(A/C exit=0)**:日志被 agent 同路径编译覆盖,仅存退出码文本
  (`verification/checkpoints/2026-09-18-1345-incident/`,README 说明)——**证据降级,
  不足以复现**。C 已由 15:2x 全量重验收取代(fcc2822);A 的正性块曾绿是合理预期,
  但接管者须以新鲜编译为准。
- 14:18 快照轮(三路中间态:A 5 错/B 4 错/C 7 错)归档完好,sha256 校验通过;
  其可复现性已被重复编译验证(同快照→同结果)。

## 5. 接管者的执行清单(按序)

1. **收敛 M1-A**(6 错,文件已 696 行,曾全绿):对照规范 §2 签名;首错 488 行
   `measure_mono_null`(mathlib v4.31 可能改名,查 `Measure.measure_mono_null`/
   `MeasureTheory.Measure.measure_mono_null` 现名)。绿 → 协议归档 → 提交。
2. **收敛 M1-B**(2 错:764 whnf 超时→拆 calc/set 收缩项;822 unsolved)。
   绿后确认 S²=K、B=S∘M∘S 定义式绑定、A7 界、矩阵公式三件齐全(规范 §3)→ 归档提交。
3. **派发 M1-D2**(契约就绪,规范 §5):新文件 `Hurst/EquivalentKernelSpectrum.lean`;
   step0 ι 可数化(可分性)、step1 A8 恒等式(已落地)、step2 三项收敛
   (B 压缩/核 L²/A4 扰动估计)、step3 取极限、step4 k 步核迭代(已落地工具)、
   step5 加权认同(已落地);产出 `diagSum_B_eq_weightedCycle` +
   `exists_weightedRieszSpectrum_min`;**ω := equivalentKernel r 实例化**
   (hm=continuous ⇒ measurable,hess=bounded ⇒ a.e. 界)。
4. **M1 验收**:聚合 import + `lake build`(写 build.log)+ AxiomAudit 追加 +
   三件套重生成 + `verify_axioms.py`;更新 VALIDATION_PROGRESS 与本文件。
5. **然后**按 §1 顺序:阻断 2(eventual 传播)、阻断 3(W8–W9 归一化能量重做 P5)、
   阻断 4(23:B–D 一般带符号)、最终端点组装。

## 6. 资产与雷区

- **可复用资产(已提交,勿动)**:P1 实际谱幂和(`P1ActualPowerSums`)、
  通用 HS/Parseval/核复合工具(`TensorParsevalTracePair`、`TOpComposition`、
  `GeneralKIntegrabilityClosed`、`RieszSectionBounds`、`EigenTraceBridge`、
  `TracePairCycle`、`FiniteMatrixTraceCycle`、`EndLevelTraceBridge`)。
  条件化组装层(CapstoneV3Closed、GeneralKHasSumFinal)**保留但注明 hconst 不可满足**,
  修复状态已在 TRANSITION_session3 更正横幅声明——不要删除,也不要据其宣称完成。
- **雷区**:① 任何带 `hconst` 的定理不能实例化到实际模型;② S=√K 非 HS
  (κ_n=1/(n+1) 反例),A7 只给 B 的界;③ 紧性 ⇏ 谱平方可和(hBridge_clm 的 hTHS
  是必要假设,由 A7 交付);④ 非可和 tsum 的 junk 默认值不可当结论;
  ⑤ `HS.I = Icc (-1) 1`(长度 2);⑥ 审计脚本边界:check_coverage 跳过首命名空间
  非 Hurst 的模块,2519 不是全项目定理数。
- **协调机制**:另一协调 agent 每 30 分钟本地只读检查
  ([ZCODE_VALIDATION_MONITOR.md](ZCODE_VALIDATION_MONITOR.md));建议通过
  VALIDATION_PROGRESS.md 传递状态,纠偏建议会由用户粘贴过来。

## 7. 验证快照(2026-09-21 17:02)

- HEAD `7814f84`;工作树未跟踪:A/B 两中间态文件 + 审查/监控文档
  (SESSION3_INDEPENDENT_REVIEW、Session3PremiseAudit、ZCODE_VALIDATION_MONITOR)。
- M1-B 首错 764:whnf 超时(800000);822:unsolved。M1-A 首错 488:
  `measure_mono_null` 未知名。接管时新鲜编译日志:`/tmp/takeover-{UnweightedRieszOperator,PositiveSquareRoot}.log`。
- 聚合 `Hurst.lean` 不含 A/B/C/A8/D1 新模块(M1 验收时统一接入);
  mathlib v4.31.0,Lean 4.31.0,arm64。
