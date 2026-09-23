# Session-4 → takeover-4 接手任务书(2026-09-23;接管者 2 第二轮后生成)

你在 Lean 4 项目 `/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
中工作(Lean 4.31.0,mathlib v4.31.0,arm64),接手 Hurst 函数估计验证 Session-4
里程碑 M1(消除不可满足前提 hconst)的**最后一块:压缩恒等式**。工作目录即
该子目录;git 已最新(HEAD `ea09fb9`,工作树仅协调员监控文件未跟踪改动,勿动)。

必读文档(按序,接手前先读完):
1. `VALIDATION_PROGRESS.md` — 置顶块(2026-09-23 更新)是最新状态;
2. `TRANSITION_session4_2026-09-21.md` — §0 快照、§10(已落地表、§10.3 A4 记录、
   §10.4 下一步、**§10.5 mathlib v4.31 雷区清单——实测,必读**)、§4(流程纪律,
   含落地前偏差自查);
3. `milestone1_hconst_elimination_math_spec.md` — M1 权威契约(§2/§3/§4 冻结签名、
   §5 D2 路线 + 2026-09-22 落地回写、§6 验收标准);
4. `Hurst/EquivalentKernelSpectrum.lean` 与 `Hurst/BopCompactness.lean` 文件头 —
   D2 已落地/未落地的诚实边界。

硬性政策(用户指示,违反必返工):
- **停用 subagent**:一切形式化由你亲自完成,不派发、不委托。
- **落地前偏差自查**(TRANSITION §4):每块完成后对照冻结契约核对 (a) 等号/不等号
  方向与三角不等式合法性;(b) 前提是否真的被消费、文档有无宣称超出签名;
  (c) 签名与规范逐字比对。
- **编译证据纪律**:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >>
  /tmp/<log>`(全量重定向+真实退出码,禁止 `| head`);验收 ≠ 编译绿:公理审计
  ⊆ {propext, Classical.choice, Quot.sound} + 检查点四件套
  (`verification/checkpoints/<日期时刻>-<track>/`:源码快照+完整日志+sha256.txt
  目录内裸名)。
- **每块落地即跟进**:新鲜编译 → 检查点归档 → git 提交 → 部分集成进 `Hurst.lean`
  跑增量 `lake build` → 更新 VALIDATION_PROGRESS 与 TRANSITION(随时回写,
  协调 agent 每 30 分钟只读检查)。
- **小块先行**:先落可编译小块;单声明同一错误卡壳 >2 次:贴 `trace_state`
  目标原文求助,不要静默硬磨。

已落地(勿重做;全部 exit=0、零 sorry、公理 ⊆ 三条、检查点+提交齐全):
- M1-A `Hurst/UnweightedRieszOperator.lean`;M1-B `Hurst/PositiveSquareRoot.lean`
  (mulOperator/sqrtOp/`exists_B_selfAdjoint_hs`/`Bop_A7_matrix_summable_bound`);
  M1-C `Hurst/EndLevelTraceBridge.lean`(`hBridge_clm`/`exists_diag_enumeration_clm`);
  A8 `Hurst/FiniteMatrixTraceCycle.lean`;D1 `TracePairCycle.lean`;
  D2-pre `Hurst/CountableEigenfamily.lean`;
- A4(d1a2f37):`Hurst/TracePerturbationEstimate.lean` 的
  `diag_pow_sub_diag_pow_le`;
- **D2 核侧无 hconst**(ff550a3):`diagSum_TOpRiesz_pow_eq_weightedCycle`
  (∀k≥2 ∀基:∑'⟪(TOp(rieszKernel psi c omega)^k)(e i),e i⟫ =
  weightedRieszCycleIntegral k,含可和性)+ 截面界六件套无 hconst 版;
- **D2 B 侧**(b2007ec):`exists_Briesz_selfAdjoint_A7`(自伴+√(κᵢκⱼ) 矩阵公式+
  A7 界 hTHS 形)+ equivalentKernel r 实例化两推论;
- 验收机械件+旧线注记+规范回写(b3119f7);
- **B 紧性(c0a72c7)**:`Hurst/BopCompactness.lean` 的
  `sqrtOp_isCompactOperator`/`Bop_isCompactOperator`;
- **B 谱枚举组装(b8eac1b)**:`exists_Briesz_spectral_enumeration`(模型 B 带乘性
  精确、平方可和的谱枚举 (val,vec),且 ∀k≥2:幂对角 HasSum 到 ∑'val^k——经
  hBridge_clm,A7 界供 hTHS);
- **压缩恒等式 step-0 前置件(18c9aa7)**:`prod_sqrt_cycle_eq`(循环 telescoping
  ∏√(κ_{i_j}κ_{i_{j+1}}) = ∏κ_{i_j})+ `diag2_symmetric_eq_sumSq`
  (⟪B²x,x⟫ = ‖Bx‖² + 对角可和性)。

诚实缺口(M1 验收未通过的唯一原因):**压缩恒等式 Diag_k(B) = Diag_k((WK)^k)**。
落地后与 `exists_Briesz_spectral_enumeration`(B 侧)+ `diagSum_TOpRiesz_pow_eq_weightedCycle`
(核侧)合成即得 `diagSum_B_eq_weightedCycle` + `exists_weightedRieszSpectrum_min`,
M1 验收复审即过。

任务顺序:

**任务 1(先做,建议闭环 k=2——价值独立成立)**:
- 子引理 ①(基↔特征族矩阵平方**等式**):
  `∑'_{p:ℕ²} ⟪e p.1, B e p.2⟫² = ∑'_{q:ι²} ⟪v q.1, B v q.2⟫²`
  (B 对称前提;照抄 `A7_aux` 的 ENNReal calc 链——其每一步都是等式步
  (tsum_prod'/tsum_comm/ofReal_tsum_of_nonneg/pee/pvv/hflip),只去掉最后的
  ≤ 收尾;hflip 步需要 hBsym;ℝ-可和性结论用 A7_aux 尾部的
  summable_of_sum_le + toReal 骨架)。~40 行。
- 子引理 ②(核侧 k=2 展开):
  `∑'_i ⟪T_R² e_i, e_i⟫ = ∑'_{ι²} κ_i κ_j ⟪v_i, W v_j⟫²`。
  参考:`cycle2_eq_tsum_pair`(已落地)给出 cycle2 的基-乘积和形;
  `tracePair_comp_tsum` 的证明里有逐纤维 Parseval 骨架;T_R v_j = κ_j W v_j
  供给矩阵条目;W 对称(实值 ω)给 ⟪v_j,W v_i⟫ = ⟪v_i,W v_j⟫ 坍缩。
- 组装:`diag2_B_eq_weightedCycle`——
  ∑'val² [exists_Briesz_spectral_enumeration 的 k=2 HasSum]
  = ∑'‖B e_i‖² [diag2_symmetric_eq_sumSq]
  = ∑'_{ℕ²}⟪e,B e⟫² [Parseval 逐列]
  = ∑'_{ι²} κᵢκⱼ⟪vᵢ,Wvⱼ⟫² [子引理 ① + inner_Bop_matrix]
  = ∑'_i ⟪T_R² e_i, e_i⟫ [子引理 ②]
  = weightedRieszCycleIntegral 2 [tracePair_comp_tsum +
  cycle2_rieszKernel_eq_weighted,均已落地]。
  即 CapstoneV3 的 hTwo 在无 hconst 线上的完整复现。

**任务 2:一般 k 的截断路线**(若 k=2 顺利再攻):
- P_N := v-族前 N 项张成正交投影(`Submodule.span ℝ (v '' Finset.range N)`
  的 starProjection;可数性由 CountableEigenfamily 供给);B_N′ := P_N B P_N。
- A8(`trace_pow_eq_cycleSum`/`trace_Bm_eq_cycleSum`,已落地)给有限矩阵迹恒等式;
- A4(`diag_pow_sub_diag_pow_le`,已落地)给 Diag_k(B_N′) → Diag_k(B)
  (op+HS 界由 A7 结论供给,幂对角可和性由 B 枚举+有限维供给);
- 截断循环和 → (WK)^k 对角:核 L² 收敛 (b),无 hconst 截面界 package
  (`rieszKernel_sectionBounds_nohconst`/`compPowR_section_aux`,已落地);
- 产出 `diagSum_B_eq_weightedCycle` + `exists_weightedRieszSpectrum_min`
  (与 `exists_Briesz_spectral_enumeration` 合成)。

**任务 3:M1 验收复审**(契约 §6):两步落地后聚合补齐 + `lake build Hurst`
(写 build.log)+ AxiomAudit 追加 + check_coverage/verify_axioms 重跑 +
实例化声明写入 VALIDATION_PROGRESS。**此前不得宣称 M1 验收通过。**

**任务 4(若余量)**:按 TRANSITION §1:阻断 2(eventualCard 传播)→ 阻断 3
(P5 归一化能量 W8–W9)→ 阻断 4(23:B–D 一般带符号;可复用
`rieszKernel_section_sq_col` 的无 hconst 手法)→ 端点组装。

mathlib v4.31 雷区(两轮实测汇总,全表见 TRANSITION §10.5):
`ring` 只关等式目标(≤ 用 `le_of_eq (by ring)`);`Finset.sum_const` 的加数 b 是
**显式**参数且仅限常量加数;`∑'` 记号在括号内会吞掉尾随 `+ 1`(先把 tsum
命名为实数);无 `tsum_sub`/`Finset.mem_toFinset`/`Subset.rfl`(用
`HasSum.sub.tsum_eq`/`Finset.mem_coe`/`Set.Subset.rfl`);`finRotate` 是根级名
(非 Fin.finRotate);`⌈·⌉` 默认 ℤ(ℕ 用 Nat.ceil);此版 **IsSymmetric 方向为
`inner (B x) y = inner x (B y)`**(与旧注记相反!);`↑B` coercion 在 show/rw
实参中目标未知时报 invalid coercion——需全标注 `(B : L2 →ₗ[ℝ] L2)`;
`Measurable.pow` 的指数是可测函数;RieszSectionBounds/GeneralKHasSumFinal 的
关键助手多为 private(跨文件不可见须本地复刻,EquivalentKernelSpectrum/
BopCompactness 已复刻一批可参考);`set K := …` 折叠后引理隐参须显式命名传参;
项级 `(fun u => by …)` 作引理实参会让隐参合成失败(改具名 have);错误恢复会
掩盖后续段真错误,中间态错误清单不可信,一切以新鲜全量编译为准。

汇报要求(诚实条款,不变):
landed/not-landed 分列、conditional/unconditional 分列、签名偏差声明式回写
规范与 TRANSITION、编译日志路径+真实退出码+公理审计输出、已知缺口——不许把
缺口写成"机械步骤"收尾;**压缩恒等式落地并复审前,不得宣称 M1 验收通过**。
