# Session-4 → takeover-3 接手任务书(2026-09-22 15:3x;接管者 2 生成)

你在 Lean 4 项目 `/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
中工作(Lean 4.31.0,mathlib v4.31.0,arm64),接手 Hurst 函数估计验证 Session-4
里程碑 M1(消除不可满足前提 hconst)的**收官两缺口**。工作目录即该子目录;
git 已最新(HEAD `f297fad`,工作树仅协调员监控文件未跟踪改动,勿动)。

必读文档(按序,接手前先读完):
1. `VALIDATION_PROGRESS.md` — 置顶块(2026-09-22 15:1x 收官块)是最新状态;
2. `TRANSITION_session4_2026-09-21.md` — §0(本轮收官快照)、§10(已落地表、
   §10.3 A4 记录与自查、§10.4 下一步、**§10.5 mathlib v4.31 雷区清单——实测,
   必读**)、§4(流程纪律,含落地前偏差自查);
3. `milestone1_hconst_elimination_math_spec.md` — M1 权威契约(§2/§3/§4 冻结签名、
   §5 D2 路线 + 2026-09-22 落地回写、§6 验收标准);
4. `Hurst/EquivalentKernelSpectrum.lean` 文件头 — D2 已落地/未落地的诚实边界。

硬性政策(用户指示,违反必返工):
- **停用 subagent**:一切形式化由你亲自完成,不派发、不委托。
- **落地前偏差自查**(TRANSITION §4 新增):每块证明完成后对照冻结契约核对
  (a) 等号/不等号方向与三角不等式合法性;(b) 前提是否真的被消费、文档有无
  宣称超出签名;(c) 签名与规范逐字比对。
- **编译证据纪律**:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >>
  /tmp/<log>`(全量重定向+真实退出码,禁止 `| head` 管道);验收 ≠ 编译绿:
  公理审计 ⊆ {propext, Classical.choice, Quot.sound} + 检查点四件套
  (`verification/checkpoints/<日期时刻>-<track>/`:源码快照 + 完整日志 + sha256.txt
  目录内裸名)。
- **每块落地即跟进**:新鲜编译 → 检查点归档 → git 提交 → 部分集成进 `Hurst.lean`
  跑增量 `lake build` → 更新 VALIDATION_PROGRESS 与 TRANSITION(随时回写,
  协调 agent 每 30 分钟只读检查 VALIDATION_PROGRESS)。
- **小块先行**:先落可编译小块;单声明同一错误卡壳 >2 次:贴 `trace_state`
  目标原文向用户/协调方求助,不要静默硬磨。

已落地(勿重做;全部 exit=0、零 sorry、公理 ⊆ 三条、检查点+提交齐全):
- M1-A `Hurst/UnweightedRieszOperator.lean`(§2 冻结接口全齐:无权算子对称/HS/紧/
  A5 正性/完备非负特征族 `exists_nonneg_eigenfamily`);
- M1-B `Hurst/PositiveSquareRoot.lean`(mulOperator 层、sqrtOp 层 `exists_positive_sqrt`、
  `Bop` 绑定 + `inner_Bop_matrix` + `A7_aux` + `Bop_A7_matrix_summable_bound` +
  `exists_B_selfAdjoint_hs`;`measurable_equivalentKernel`/`aeBounded_equivalentKernel`);
- M1-C `Hurst/EndLevelTraceBridge.lean`(`hBridge_clm`/`hBridge_clm_tsum`/
  `exists_diag_enumeration_clm`);A8 `FiniteMatrixTraceCycle.lean`
  (`trace_pow_eq_cycleSum`/`trace_Bm_eq_cycleSum`);D1 `TracePairCycle.lean`(非承重);
- D2-pre `Hurst/CountableEigenfamily.lean`(`instSeparableSpaceL2` 无条件、
  `countable_of_orthonormal`、`exists_injective_to_nat`);
- A4 `Hurst/TracePerturbationEstimate.lean`(d1a2f37):`diag_pow_sub_diag_pow_le`
  + 无条件层 + CS 配对助手;
- **M1-D2 部分**(ff550a3/b2007ec):`Hurst/EquivalentKernelSpectrum.lean` —
  `diagSum_TOpRiesz_pow_eq_weightedCycle`(核侧迹幂恒等式,**无 hconst**,
  ∀k≥2 ∀基:∑'⟪(TOp(rieszKernel psi c omega)^k)(e i),e i⟫ =
  weightedRieszCycleIntegral k)+ 截面界六件套无 hconst 版
  (`rieszKernel_sectionBounds_nohconst`/`hP_rieszKernel_nohconst`/
  `rieszKernel_section_sq_col`)+ `exists_Briesz_selfAdjoint_A7`(模型 B 全套
  结构包:hTHS 形 A7 界在结论,可直接喂 hBridge_clm 的 hTHS 槽)+
  `diagSum_TOpRiesz_pow_eq_weightedCycle_equiv`/`exists_Briesz_selfAdjoint_A7_equiv`
  (ω := equivalentKernel r 实例化,模型前提全消解);
- 验收机械件(b3119f7):AxiomAudit 35 行、build.log 绿、脚本全过;
  旧线 `rieszSpectrumVal_*`/`CapstoneV3Closed` 已注明 hconst 不可满足。

诚实缺口(M1 验收未通过的原因;按序做):

**任务 1(先做):B 紧性** —— `IsCompactOperator (Bop hv he hκ0 omega hm hess)`。
已勘察路线(数学无误,Lean 工作量约一个检查点周期):
- `∑κ² < ∞ ⇒ κ i → 0`(mathlib `Summable.tendsto_atTop_zero` 一类,名字以实测为准)
  ⇒ 尾部 sup `√κ_i → 0`;**注意 ∑κ < ∞ 并不成立**(反例 κ=1/(n+1)),但紧性只需要
  κ→0,不需要 ∑κ;
- 截断 `S_N`(谱系数取 i<N):像含于有限维 `span{v i | i<N}` ⇒ 有限秩;有限维靶上
  `id` 素(`isCompactOperator_id_iff_finiteDimensional`/
  `isCompactOperator_of_locallyCompactSpace_dom`),经
  `IsCompactOperator.clm_comp` 得 `S_N` 紧;
- `‖S − S_N‖ ≤ sup_{i≥N} √κ_i → 0`(尾部 Parseval 上界;需要从已落地 specPair/
  specOperator 机制出发证一个尾部版范数界,这是本块主要工作量)+ mathlib
  `isCompactOperator_of_tendsto` ⇒ S=sqrtOp 紧;
- `B = S ∘L (mulOperator ∘L S)` 由 `IsCompactOperator.clm_comp` 紧(紧∘连续)。
- 落点建议:`Hurst/EquivalentKernelSpectrum.lean` 追加(或新文件
  `Hurst/BopCompactness.lean`);勿改 `PositiveSquareRoot.lean` 既有声明(可追加)。
  落地后即可把 `exists_diag_enumeration_clm`+`hBridge_clm` 应用到 B。

**任务 2:压缩恒等式 Diag_k(B) = Diag_k((WK)^k)**(A8–A9 路线 step0–3,剩余
最大块;组装目标本轮已勘察定形):
- Diag_k(B) = lim_N Diag_k(B_N′)[B_N′ = P_N B P_N,用 A4 的
  `diag_pow_sub_diag_pow_le`:op+HS 界由 A7(`exists_Briesz_selfAdjoint_A7` 结论)
  供,hXabs/hYabs 幂对角可和性对 B_N′ 由有限维 + 对 B 由 hBridge_clm(任务 1 后)
  供,HS 收敛 ‖B_N′−B‖→0 由 A7 界 + 截断尾部趋零];
- = lim_N tr((B_N′ 的有限矩阵)^k)[A8:`trace_Bm_eq_cycleSum`,κ≥0 条件在
  `inner_Bop_matrix` 的 √(κᵢκⱼ) 非负性处满足];
- = lim_N Diag_k((W K_N)^k)[K_N = B_N′ 对应的有限秩无权核截断;两矩阵的循环和
  逐项相等:√(κᵢκⱼ)⟪vᵢ,W vⱼ⟫ 两侧同形];
- → Diag_k((WK)^k)[核 L² 收敛 (b):无 hconst 截面界 package 已落地,
  `compPowR_section_aux`/`sectionCS` 可复用];
- 右端已由 `diagSum_TOpRiesz_pow_eq_weightedCycle` 闭合到
  `weightedRieszCycleIntegral k psi c omega`。
- 缺:截断族构造(K_N/B_N′ 与投影 P_N 的 Lean 形态)、收敛 (a)(b) 的证明、
  有限矩阵迹与有限秩算子迹的桥(A8 是纯 `Matrix` 层)。
- 产出:`diagSum_B_eq_weightedCycle` + `exists_weightedRieszSpectrum_min`
  (组装 `hBridge_clm`+`exists_diag_enumeration_clm`(B 紧性后)+主恒等式)。

**任务 3:M1 验收复审**(契约 §6):两缺口落地后聚合补齐 + `lake build Hurst`
(写 build.log)+ AxiomAudit 追加新定理 → 三件套 + 脚本重跑 + 实例化声明写入
VALIDATION_PROGRESS(实例化推论已在,验收时只需引用并复核其无 hconst)。

**任务 4(若余量)**:按 TRANSITION §1 顺序:阻断 2(FullChainEndpoint
eventualCard 传播,先例 `..._signed_eventualCard`)→ 阻断 3(P5 归一化能量
W8–W9)→ 阻断 4(23:B–D 一般带符号;注意 `rieszKernel_sectionBounds_package`
的 hconst 仅用于列向界常数化,`EquivalentKernelSpectrum.lean` 的
`rieszKernel_section_sq_col` 已示范无 hconst 替代,阻断 4 可部分复用)→ 端点组装。

mathlib v4.31 雷区(实测新增,详见 TRANSITION §10.5 全表):
`ring` **只关等式目标**,≤ 用 `le_of_eq (by ring)`/nlinarith;项级
`(fun u => by …)` 作引理实参会令隐参(如 `summable_of_sum_le` 的 `c`)合成失败,
改具名 `have` 整块传入;`Measurable.pow` 的指数是**可测函数**非数值
(`.pow measurable_const`);`RieszSectionBounds`/`GeneralKHasSumFinal` 的关键助手
多为 **private**(跨文件不可见,需本地复刻——`EquivalentKernelSpectrum.lean`
已复刻一批可参考);`set K := …` 折叠后,引理隐参常需显式命名传参
(`(psi := psi) (c := c)`);错误恢复会掩盖后续段真错误,中间态错误清单不可信,
一切以新鲜全量编译为准。

汇报要求(诚实条款,不变):
landed/not-landed 分列、conditional/unconditional 分列、签名偏差声明式回写
规范与 TRANSITION、编译日志路径+真实退出码+公理审计输出、已知缺口——不许把
缺口写成"机械步骤"收尾;**完成前不得宣称 M1 验收通过**。
