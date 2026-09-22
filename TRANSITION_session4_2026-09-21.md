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

## 4. 开发与测试流程(subagent 编排与即时跟进)

本节是本轮验证实际运转并验证有效的编排流程,接管者照此执行。

### 4.1 总循环:数学契约 → 并行形式化 → 落地即跟进 → 集成验收

每个里程碑按四相推进,任何一相不达标不进入下一相:

1. **契约相(主 agent)**:写数学规范(如 `milestone1_*.md`)——冻结定理签名、
   每个前提的"实际模型中如何消解"表、路线注释、预期缺口。契约是**可证伪初稿**:
   执行中发现的错误(本轮 7 处:hc、假合取、本质有界、HS 条件等)必须声明式回写。
2. **派发相(主 agent → 3–5 路 subagent)**:见 4.2。
3. **跟进相(主 agent,不等全)**:见 4.3。
4. **集成验收相(主 agent)**:见 4.4。

### 4.2 subagent 派发纪律

- **3–5 路并行,文件互斥**:每个 agent 恰好拥有一个新文件,绝不共写;
  需要他人产出时以"冻结契约签名"为接口先行起草(条件化),不阻塞等待。
- **任务书自包含**(agent 无会话记忆):①契约签名(逐字)+ 数学路线;
  ②已落地工具地图(文件名+定理名,注明"READ first, import and glue, 勿重证");
  ③编译协议(全量日志+真实退出码+单文件 lake env lean,禁 head 管道);
  ④验收标准(exit 0、零 sorry、公理⊆三条、签名偏差须声明);
  ⑤诚实报告要求(landed/not-landed、conditional/unconditional 分列,
  不许把缺口写成"机械步骤"收尾)。
- **解耦模式**:下游定理把上游结论打包为显式假设先编译通过(可立即验证组装
  逻辑),上游落地后追加一行无条件推论。**反例警告**(本轮教训,审查前必须
  检查):打包假设必须在全量词域上可满足——∀k hPair(k=1 假)、∀r 塔界+单一 E
  (hsNorm>1 无解)、hconst(全域量词)都是不可满足打包,会使定理变空真。
- **小块先行**:任务书明确"先落可编译小块并报最小编译检查点";
  单点卡壳 >2 次同一错误 → agent 上报 trace_state 目标原文,主 agent 直接给修正项
  或介入缩小目标;禁止 agent 长时间静默磨同一错误。
- **依赖解锁通知**:上游落地→主 agent 用 SendMessage 把最终签名(含任何偏差)
  即时发给在途下游;agent 因配额中断→快照其中间态+写交接,重启时按"续作"派发
  (先编译评估真实剩余,不重做)。

### 4.3 落地即跟进(核心原则:不等全员到齐)

subagent completion report 一到,主 agent **立即**依次执行(本轮标准动作,全程
分钟级,不与其它在途 agent 冲突):

1. **验证**:对落地文件新鲜全量编译(不信任 agent 报告里的日志)+ `lake build`
   产 olean + `#print axioms`(临时 /tmp scratch 文件,不入库)。
2. **归档**:按检查点协议四件套(§3.1)存 `verification/checkpoints/<时刻>-<件>/`。
3. **提交**:git add(文件+检查点目录),commit message 写明交付物与偏差。
4. **传播**:解锁依赖 SendMessage;能立即消费的部分(如 import 下游、装配推论)
   马上做;**部分集成**——每落一个模块就 import 入 `Hurst.lean` 跑增量 `lake build`,
   不攒到收官(及早暴露聚合层冲突;本轮两次部分集成均提前发现命名空间/审计问题)。
5. **同步**:`VALIDATION_PROGRESS.md` 回填(定理清单、日志路径、退出码、剩余对象),
   供协调 agent 30 分钟只读检查。

### 4.4 集成与测试验收(每里程碑一次)

1. 全部新模块 import 入 `Hurst.lean`(注意命名空间:多数模块在根级 `HS.*`,
   审计行前缀写错会产生 unknown-constant 混入日志)。
2. `lake build Hurst > verification/build.log 2>&1`(真实退出码,日志尾部须有
   `Build completed successfully`);此前**先等所有在途编译结束**(本轮曾发生
   /tmp 与归档路径的双重竞写——归档目录必须专属,重跑前检查无同名任务在途)。
3. `verification/AxiomAudit.lean` 追加新定理的 `#print axioms` 行 →
   `lake env lean verification/AxiomAudit.lean > verification/axioms.log`
   (0 个 `error:`;名字含 "error" 的定理不算)。
4. `python3 scripts/check_coverage.py` + `python3 scripts/verify_axioms.py`
   (后者会捕捉 coverage-审计漂移:模块提交了但未入聚合→缺名断言失败,本轮
   P2CloseoutV2 即此例)。
5. **适用性验收 ≠ 编译绿**:对里程碑目标定理给出实际模型实例化
   (M1:ω := equivalentKernel r,hm/hess 由 `equivalentKernel_continuous`/
   `equivalentKernel_bounded` 消解)并写入进度文件;无法实例化的部分列入
   "未消解前提",不得宣称完成。
6. 检查点目录、进度文件、交接文档(如里程碑收官)一并提交。

### 4.5 监控与纠偏接口

- 协调 agent 每 30 分钟本地只读检查 `VALIDATION_PROGRESS.md`(其配置见
  [ZCODE_VALIDATION_MONITOR.md](ZCODE_VALIDATION_MONITOR.md));主 agent 保持该文件
  **每次状态变化即更新**(当前里程碑、变更文件、已运行验证+日志路径+退出码、
  未消解前提、下一步)。
- 协调方的快照诊断分发前,先对最新源码重编译核对(快照滞后于活文件,
  避免重修已解决的问题——本轮多次发生,已验证有效)。
- 用户/协调方的纠偏建议按"先通知在途 agent(带时效提醒)→ 回写规范 → 更新进度
  文件 → 提交"的顺序落实;与在途 agent 冲突的指示等其当前编译轮结束再应用。

## 5. 历史检查点与证据等级(诚实记录)

- **13:45 检查点(A/C exit=0)**:日志被 agent 同路径编译覆盖,仅存退出码文本
  (`verification/checkpoints/2026-09-18-1345-incident/`,README 说明)——**证据降级,
  不足以复现**。C 已由 15:2x 全量重验收取代(fcc2822);A 的正性块曾绿是合理预期,
  但接管者须以新鲜编译为准。
- 14:18 快照轮(三路中间态:A 5 错/B 4 错/C 7 错)归档完好,sha256 校验通过;
  其可复现性已被重复编译验证(同快照→同结果)。

## 6. 接管者的执行清单(按序)

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

## 7. 资产与雷区

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

## 8. 验证快照(2026-09-21 17:02)

- HEAD `7814f84`;工作树未跟踪:A/B 两中间态文件 + 审查/监控文档
  (SESSION3_INDEPENDENT_REVIEW、Session3PremiseAudit、ZCODE_VALIDATION_MONITOR)。
- M1-B 首错 764:whnf 超时(800000);822:unsolved。M1-A 首错 488:
  `measure_mono_null` 未知名。接管时新鲜编译日志:`/tmp/takeover-{UnweightedRieszOperator,PositiveSquareRoot}.log`。
- 聚合 `Hurst.lean` 不含 A/B/C/A8/D1 新模块(M1 验收时统一接入);
  mathlib v4.31.0,Lean 4.31.0,arm64。
