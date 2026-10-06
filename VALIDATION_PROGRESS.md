# VALIDATION_PROGRESS（供协调 agent 检查；持续更新）

更新:2026-10-05(Session-4 takeover6;**阻断 2/3/4 全部关闭 + 端点组装落地**;
同时审计并落定了 2026-09-26 并行修复 session 的未提交工作;历史块在下)。

> 交接状态(2026-10-05 更新):任务书 = takeover6(阻断 2 → 3 → 4 → 端点组装,
> 顺序执行,commit 65aa208,检查点 `verification/checkpoints/2026-10-05-1827-mainline-blockers234-endpoint/`)。
>
> **前置说明(工作区来源)**:接手时工作区非干净——2026-09-26 的并行修复
> session(用户当时授权 subagent 且禁止 commit,见 COORDINATION_2026-09-26.md)
> 留下 11 个未跟踪新件 + 4 个修改件,其中 `GeneralSignedPowerMatching.lean`
> 从未完整编译(5 处错误)。本轮全部形式化由主 agent 亲自完成:先审计该批
> 工作,修复其唯一失败模块,再补齐组装。前 session 的两个检查点
> (2026-09-26-Normalized{Actual,Hermite}Energy)随历史记录一并入库。
>
> **阻断 2(eventualCard 传播)关闭**:
> - FullChainEndpoint 三处端点(原行 158/318/382)的 `hm : ∀ n, 0 < card`
>   已移除;P5LogHLayers Layer 1 与 P5SeamClosed seam 改经
>   `CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard`
>   (D3 安全零填充先例,eventual 非空由 card/S → 2 内部派生;空行 Fin 0 空真)。
> - `session3_fullChain_all_rows_impossible` 指向的旧形态已不存在
>   (审计文件按任务书保留原样)。
>
> **阻断 3(P5 归一化能量 W8–W9)关闭**:
> - 新件五枚:`NormalizedHermiteEnergy`(realScaleMeshEnergy 精确归一化恒等式
>   S^(2ψ−2)、近/远带四阶余项 ≤ U²(带能量+ε²·总能量)、
>   `gaussian_array_rank_second_moment_double_sum`(Hilbert 空间二阶矩
>   双和界,保成对相关而非行最大)、double-sum 版 log 极限)、
>   `NormalizedActualEnergy`(`hurstHolder_q1_actual_normalized_energy_eventually_bounded`:
>   实际模型 S^(2ψ−2)·∑∑ρ² = O(1),由闭 HS→Riesz 网格逼近 + Riesz 参考能量,
>   消解表见文件头)、`NormalizedActualRemainder`
>   (`hurstHolder_q1_actual_weighted_fourth_tendsto_zero`:S^(2ψ)·∑∑|w_iw_j|ρ⁴ → 0,
>   hEnv 对任意固定常数成立以解耦两个存在见证)、`NormalizedLogVariance`
>   (单位权方差 ≤ 4·V·U²·S^(−2ψ)、裁剪窗 → 0)、`NormalizedLogProjection`
>   (归一化能量下的 L1 投影收敛)。
> - **矛盾定理已入档**:`verification/Session4Blocker3Audit.lean` 的
>   `session4_unnormalized_hE2_impossible`(新引理 `featureCorrelation_self`:
>   对角 ρ_ii = 1;对角和 ≥ card → ∞ 与 ∃C 上界矛盾;公理三条)。
>   旧 hE2(未归一化)自 FullChainEndpoint 主线移除。
>
> **阻断 4(一般符号极限 23:B–D)关闭**:
> - 新件六枚:`IntervalL2Basis`(区间指示族 → 内部构造 HilbertBasis ℕ,
>   关闭外部基供给漏洞)、`WeightedRieszSpectrumClosed`
>   (`exists_weightedRieszSpectrum_equiv_closed`:仅 0<ψ、2ψ<1、0<c 三前提)、
>   `GeneralSignedPowerMatching`(B1 Weierstrass 连续测试、正/负部平方后
>   非负剥离、antitoneResort+layer-cake 排序 profile、
>   `signed_sorted_coefficients_tendsto`(无任何逐行非空前提,平移过坏行)、
>   `signedInterleavedRow_matching_data`/`_tendsto_secondChaos_of_powerSums`)、
>   `SignedInterleavedLaw`(符号感知置换 = 零填充原行的置换,含空行/重根)、
>   `SignedPowerLimit`(`centeredSpectralSquares_tendsto_of_signed_powerSums`:
>   全部幂和 → 构造二阶混沌;`exists_centeredSpectralSquares_limit_*`)、
>   `ActualQ1SignedClosed`(`actualQ1LongStatistic_tendsto_secondChaos_generalSigned`:
>   可行带宽二次端点,极限律为构造的加权 Riesz 二阶混沌;无 hNegMass、
>   无 hlam 反序非负包、无 hQ、无仅偶次 hPow)。
>   P3SignedMatching 行 178/429 的 hNegMass 与 interleaved 分布认同缺口
>   均不再被主线消费(新线经 SignedInterleavedLaw 的恒等分布 + 构造极限)。
>   **本文件由本轮修复到 exit=0**(前 session 留下 5 错:neg_pow 的 simp
>   自环(RHS 含 (−1)^k 自匹配)改 rw 逐点改写;HasSum.even_add_odd 点记法
>   高阶统一 whnf 超时改显式 f 实例化;interleaved 槽位改 definitional helper + rfl)。
>
> **端点组装(任务 4)落地**:`Hurst/FullChainGeneralSigned.lean`
> - `gs_fourthEnergy_eq`(谱权双和四阶能量 ≡ q1ActiveWeightedFourthEnergy:
>   actualQ1SpectralWeight = S^ψ·localPolynomialWeights 之代数 +
>   gridStrideFirst_correlation_identity 之相关同一)+ 
>   `gs_fourthEnergy_tendsto_zero`(标量率下消解)+ 
>   `gs_logProjection_L1_tendsto_instantiated`(归一化 hJoin)+
>   Layer 1'(`actualQ1_logStatistic_tendsto_secondChaos_doubleSum`,P5LogHLayers 新增)
>   + 通用 seam 核心(`logStatistic_knownScaleH_seam_of_logLimit`,P5SeamClosed
>   新增;旧 seam 改薄包装,签名不变)。
> - **`actualQ1_knownScaleH_fullChain_generalSigned`**(truth-centered 主端点):
>   `2 n^{ψ(1−γ)} log n (Ĥ_n − f t) ⇒ −Q`,Q 为构造的 signed 加权 Riesz
>   二阶混沌律(存在性+律为结论)。前提 = 模型窗口 + hgrid + hane + 标量率
>   (hR/hcut/hEnv,消解表在文件头,先于形式化写就)+ 中心带/E5 数据。
>   **hm/hE2/hNegMass/hlam/hQ/偶次 hPow/hW0 全部从主线消失**。
>
> **聚合验收(2026-10-05 执行)**:
> 1. ✅ 全量 `lake build Hurst` 9213 jobs 绿(`verification/build.log` exit=0)。
> 2. ✅ `verification/AxiomAudit.lean` 追加 21 条关键定理(2541 行 #print axioms,
>    0 真实错误,35 个 "error" 匹配均为定理名),全部 ⊆ {propext, Classical.choice,
>    Quot.sound},0 sorryAx;定向审计 69 定理同判(日志
>    `/tmp/axiom-audit-takeover6b.log`,检查点内 axioms.log)。
> 3. ✅ 零 sorry 复查(grep 16 个涉改文件 0 命中)。
> 4. ✅ 检查点四件套(19 源快照 + compile.log + axioms.log + sha256.txt,
>    裸名哈希)。
>
> **已知缺口(诚实登记,不得粉饰)**:
> - 标量率前提(hR/hcut/hEnv)为显式前提;其在可行带宽的可满足性已在
>   消解表手推(R = ⌊n^β⌋,β < (1−γ)(1−2ψ);hEnv 第 (iii) 项消失恰为 hgrid),
>   **但显式 R 的 Lean 实例化尚未接线**——这是端点全实例化的最后一步。
> - 中心带 (cσ, d, hband) 与 E5 数据 (hE5, C, hBias) 仍为数据前提
>   (file-22-W9 / E5 口径,与 M1 分类一致)。
> - 旧 FullChainEndpoint 三定理保留为 conditional legacy(文件头已注明
>   被新主线取代);hconst 线条件文件未动(按任务书纪律)。

更新:2026-09-24(Session-4 接管者 4;**一般 k 路线第 4/5/6 节全部落地;
diagSum_Bop_eq_weightedCycle(∀k≥2)+ exists_weightedRieszSpectrum_min +
equivalentKernel r 实例化落地;M1 验收复审四项全部执行**;历史块在下)。

> 交接状态(2026-09-24 更新):任务书 = takeover5 口头任务书(Session-4 接管者 4)。
> **第 4 节(核侧极限组装)已落地**(`Hurst/CompressionGeneralK.lean`):
> - 4a(7d0684f,检查点 `2026-09-24-1628-CompressionGeneralK-s4a/`):
>   `exists_measurable_rep_family` + 张量坐标两件
>   (`tensorCoord_unweightedRiesz`/`tensorCoord_truncKernel`)+
>   **`hsNorm_sub_truncKernel_sq_eq_tail`**(HS 平方尾 = κ²-尾,张量 Parseval
>   沿对角坍缩经 `Function.Injective.hasSum_iff`,免 ι 可数化)+
>   `levelSet_finite`/`exists_exhausting_finsets` +
>   **`hsNorm_sub_truncKernel_tendsto_zero`**(核尾 → 0)。
> - 4b+4c(5b5fbe8,检查点 `2026-09-24-1644-CompressionGeneralK-s4bc/`):
>   `measurable_truncKernel`/`measurable_weightedTruncKernel` +
>   **`comp_mulOperator_kappaTruncOp_eq_TOp`**(M_ω∘T_t = TOp(ω·truncKernel))+
>   **`hsNorm_weight_mul_sub_le`**(加权差控制 ≤ MR·hsNorm(K−N))。
> - 4d(1ea0961,检查点 `2026-09-24-1733-CompressionGeneralK-s4d/`):
>   `weightedKernel_ae_rieszKernel` + `cycle2_sub_decompose`/
>   `abs_cycle2_sub_le` + **`diagTsum_pow_eq_cycle2`**(TOp C 幂对角和 =
>   cycle2(塔,顶)) + **`diagTsum_pow_weightedTrunc_tendsto`**(第 4 节主定理:
>   截断幂对角和 → 加权 Riesz 核算子幂对角和,塔 Lipschitz + 4a 尾界挤压)。
> **第 5 节(B 侧 A4 极限)已落地**(23f1f67,检查点
> `2026-09-24-1915-CompressionGeneralK-s5/`,14 定理):
> - 5a:`summable_normSq_apply_and_eq`(列平方和 = 矩阵双和,A4 的 ℓ² 供给)+
>   `BtruncOp_symm` + `BtruncOp_matrixSq_summable`(有限秩包)。
> - 5b:**`norm_sqrtOp_sub_sqrtTruncOp_tendsto_zero`**(level-set 逼近)+
>   `Bop_sub_BtruncOp_eq`(B−B_t 两项分解)+ `norm_Bop_sub_BtruncOp_le`
>   (≤ 2√‖T‖·MR·‖S−S_t‖)+ `norm_Bop_sub_BtruncOp_tendsto_zero`。
> - 5c:**`vmatrixSq_BsubBtrunc_eq_indicator`**(B−B_t 的 v-矩阵平方 = A7 族在
>   t×t 上的补指示,√-系数坍缩)+ `eMatrixSummable_BsubBtrunc`(A7_aux 运输,
>   一致界 MR²∑κ²)+ `tsum_eMatrixSq_BsubBtrunc_eq_tail`(基不变)+
>   **`diagL2_BsubBtrunc_tendsto_zero`**(对角 ℓ² 内容 → 0,完全绕开非-HS 的 S)。
> **第 6 节(最终组装)已落地**:
> - 6a(bcfd3e3,检查点 `2026-09-24-2128-CompressionGeneralK-s6a/`):
>   `summable_abs_diagTsum_pow`(A4 的 hXabs/hYabs 供给:半幂自伴分裂 + CS 配对)
>   + 四个小上下文范数 helper(`norm_sqrtOp_le'` 等逐点 opNorm 链——复合算子
>   defeq 展开在 1M 心跳下也超时,故提取为独立引理)+ 常数 Cu =
>   ‖T‖·MR + MR·√(∑κ²) 统一范数与列平方界 + **`diagSum_Bop_eq_weightedCycle`**
>   (∀k≥2 ∀Hilbert 基:B 幂对角和 = weightedRieszCycleIntegral k;
>   D_N = 2√‖T‖MR‖S−S_t‖ + √(尾) 同时满足 A4 两个 D-前提且 → 0;
>   逐 N:A4 + 3b 中段等式 + 4b 识别 + 4d 核收敛,tendsto_nhds_unique 挤压)。
> - 6b(af11726,检查点 `2026-09-24-2237-CompressionGeneralK-s6b/`):
>   **`exists_weightedRieszSpectrum_min`**(模型 B 带重数精确、平方可和谱枚举,
>   ∀k≥2 HasSum(val^k) = WRCI k;幂族可和性经
>   |val^k| = |val|^{2+(k−2)} ≤ M^{k−2}·val² 逐点支配 + summable_of_sum_le)。
> - 6c(7bc1663,检查点 `2026-09-24-2259-CompressionGeneralK-s6c/`):
>   **`exists_weightedRieszSpectrum_min_equiv`**(ω := Hurst.equivalentKernel r
>   完整实例化;权重界存在式打包——逐点界 equivalentKernel_bounded 同时充当
>   hess 的 a.e. 前提(逐点 ⇒ a.e.);hpow/hg 与可行窗口为数据前提,与旧线
>   rieszSpectrumVal 同口径;**无 hconst**)。
> **M1 验收复审(合同 §6 四项,2026-09-24 执行)**:
> 1. ✅ 全模块编译零错误零 sorry(全量 `lake build Hurst` 9201 jobs 绿,
>    `verification/build.log` exit=0);新增 16 条关键定理 #print axioms 追加进
>    `verification/AxiomAudit.lean`(2536 行,0 真实编译错误;35 个 grep "error"
>    匹配均为定理名含 "error" 字样),全部 ⊆ {propext, Classical.choice,
>    Quot.sound},日志 `verification/axioms.log` exit=0。
> 2. ✅ `exists_weightedRieszSpectrum_min_equiv` 以 ω := equivalentKernel r
>    完整实例化(阻断 1 的谱侧消除;hpow/hg/可行窗口为数据前提,合同 §1 表
>    同口径)。
> 3. ✅ 聚合 import + 全量 build + AxiomAudit 追加 +
>    `check_coverage.py` 27/27(2519 声明)+ `verify_axioms.py`
>    (sorryAx=false, custom_axioms=false, build_passed=true)。
> 4. ✅ 旧 `rieszSpectrumVal_hGen`/`*_v3_closed` 保留并注记(前轮已做)。
> **M1 验收通过(诚实口径:四项全部执行且绿;数据前提 hpow/hg/可行窗口与
> 旧线同口径,由合同 §1 表分类;无不可满足前提残留)**。
> 下一步(M1 后,按 TRANSITION §6 顺序):阻断 2(eventualCard 传播)→
> 阻断 3(P5 归一化能量 W8–W9)→ 阻断 4(一般符号 23:B–D)→ 端点组装。
> v4.31 雷区本轮新增(累积):`fun x,` 逗号形式已废除(必须 `fun x =>`);
> `HasSum.congr` 改名 `HasSum.congr_fun`(方向:新函数 = 旧);`abs_add` 根名
> 不存在(用 `AbsoluteValue.add_le AbsoluteValue.abs`);`integral_add` 方向
> 与直觉相反(左 = 右);`Orthonormal` 字段是 norm_eq_one/orthonormal' 而非
> 双参 inner 公式;`inner_sub_right`(第二参减法)vs `inner_sub_left`;
> `pow_le_pow_left₀` 需非负首参;`opNorm_le_bound` 的 f 是首显参;
> `Set.Finite.mem_toFinset`;`Real.sq_sqrt` 实例化需显式非负前提;
> `Set.indicator_of_notMem` 需 f 实参;目标在 L2 中用 `abel` 非 `ring`/
> `linarith`;`Finset.notMem_empty`;大上下文内复合算子 defeq 展开
> (Bop/BtruncOp 范数)即使 1M 心跳也超时——提取为小上下文独立引理 +
> 逐点 opNorm 链(`ContinuousLinearMap.le_opNorm` 逐级)是唯一稳定路线;
> `summable_of_sum_le` 的 c 需显式命名传参;`tsum_congr`+`congrArg` 桥接
> 算子等式到幂。

> 交接状态(2026-09-23 22:5x 留档):任务书 = `HANDOVER_PROMPT_session4_takeover4.md`。
> **k=2 压缩恒等式闭环**(d628418,`Hurst/CompressionIdentity.lean`,检查点
> `2026-09-23-1508-CompressionK2/`,8 定理公理 ⊆ 三条):
> `mulOperator_comp_TOp_riesz`(W∘T=TOp(rieszKernel),纯 a.e. congruence 无
> Fubini)+ `TOp_riesz_apply_eigenfamily` + 任意指标型张量 Parseval/cycle2 展开 +
> 子引理② `diag2_TOpRiesz_eq_kappaWeighted_matrixSum` + 子引理①
> `matrixSq_sum_eq_of_complete` + 组装 **`diag2_Bop_eq_weightedCycle`**(hTwo 的
> 无 hconst 复现)+ `tsum_Briesz_valSq_eq_weightedCycle`(∑'val² = WRCI 2)。
> **一般 k 路线第 1/2a/2b 节已落地**(全部在 `Hurst/CompressionGeneralK.lean`):
> - 第 1 节(85c05ae,检查点 `2026-09-23-1616-CompressionGeneralK-s1/`):
>   a.e. 运输三件 + `hsNorm_le_of_abs_le` + `hSKernel_weight_mul` +
>   **`mulOperator_comp_TOp_gen`**(TOp(ω·K) = M_ω∘TOp K 对一切 HS 核)+
>   `hsNorm_add_le2` + `integrable_section_prod_ae` + `compKernel_sub_ae` +
>   **`hsNorm_compPowR_sub_le`**(塔 Lipschitz ≤ 2^{r+1}(r+1)M^r δ)。
> - 第 2a 节(7eadf38,检查点 `2026-09-23-1938-CompressionGeneralK-s2a/`,
>   commit message 中时间戳笔误,以目录为准):**免可数化的耗竭尾引擎**——
>   `summable_indicator`/`tsum_split_indicator`/
>   `finset_sum_le_finset_sum_of_subset`(ENNReal 运输绕开 ℝ 上缺失的
>   CanonicallyOrderedAdd)/`tsum_finite_support`/`exists_finite_small_tail`/
>   **`tail_indicator_tendsto_zero`**(level-set 截断尾 → 0)/
>   `partial_tendsto_tsum`。
> - 第 2b 节(2a28506,检查点 `2026-09-23-2015-CompressionGeneralK-s2b/`):
>   **截断张量核**——`tsum_indicator_finset`(indicator-∑' 坍缩到有限和,
>   走 eventually-常值部分和路线)/`tensKernel`/`truncKernel` 定义 +
>   `hSKernel_tensKernel`/`hSKernel_truncKernel` + **`kpair_truncKernel`**
>   (截断核配对 = ∑_{i∈t}κᵢ⟪vᵢ,f⟫⟪vᵢ,g⟫;逐项 Fubini 用本版
>   `integral_prod_mul`(无可积性假设!)+ a.e. 代表运输到内积)。
> - 第 2c 节(8d7ddae,检查点 `2026-09-23-2156-CompressionGeneralK-s2c/`):
>   **截断谱算子**——`truncKappaCoeff`/`truncSqrtCoeff` 截断系数族(κ·χ_t 与
>   √κ·χ_t;含界引理与逐点平方引理 truncSqrtCoeff_sq)+ `kappaTruncOp`/
>   `sqrtTruncOp`/`BtruncOp` 三定义 + **`TOp_truncKernel_eq_specOperator`**
>   (截断张量核的核算子 = 截断谱算子 T_t;kpair_truncKernel + specPair 展开 +
>   tsum_indicator_finset 桥接)+ `sqrtTruncOp_comp_eq_kappaTruncOp`/
>   `sqrtTruncOp_sq`(**S_t² = T_t**)+ `BtruncOp_apply` +
>   `inner_Btrunc_matrix`(√(χ·κ) 矩阵公式,inner_Bop_matrix 的截断对应物)。
> - 第 3a 节(301e7bc,检查点 `2026-09-23-2225-CompressionGeneralK-s3a/`):
>   **有限秩矩阵平方工具**——`tsum_inner_sq_hilbertBasis_eq_norm_sq`(Hilbert 基
>   Parseval 等式)+ `tsum_eq_finset_sum_of_forall_notMem`(有限支撑 ∑' 坍缩,
>   任意符号,走 indicator 桥)+ `specOperator_apply_eq_finset_sum`(有限支撑
>   谱算子的有限和作用公式)+ **`matrixSq_summable_of_decomp`**(带有限秩一
>   分解的算子在任意 Hilbert 基下矩阵平方可和,显式界 #t·∑(‖wᵢ‖‖uᵢ‖)² —
>   正是 tracePair_cyclic 消费的 HS-包装;ENNReal Tonelli +
>   sq_sum_le_card_mul_sum_sq + A7 式运输)。
> - 第 3b 节(8f910e4,检查点 `2026-09-23-2250-CompressionGeneralK-s3b/`):
>   **有限秩 cyclicity 中段等式**——
>   **`diagTsum_Btrunc_pow_eq_diagTsum_WTtrunc_pow`**(∀k≥1 ∀Hilbert 基 e:
>   Diag_k(B_t) = Diag_k((M_ω∘T_t)^k);幂重组归纳 B_t^{n+1}z =
>   S_t((W∘T_t)^n(W(S_t z))) 消费 S_t²=T_t;W∘S_t、S_t∘(W∘T_t)^m 及两个
>   复合的秩一分解经 specOperator_apply_eq_finset_sum + adjoint_inner_left;
>   四个 HS-包装由 matrixSq_summable_of_decomp 供给;单次 tracePair_cyclic)。
>   证明内用 set-缩写 W/S/T/P 控制长项。
> **未落地(诚实登记,完成前 M1 验收不通过)**:第 4 节(核侧极限组装:
> W∘T_t = TOp(ω·truncKernel) 经 mulOperator_comp_TOp_gen +
> TOp_truncKernel_eq_specOperator;cycle2/塔比较消费 hsNorm_compPowR_sub_le,
> 把 Diag_k((W∘T_t)^k) 过渡到 Diag_k(TOp(rieszKernel)^k)——HS 范数平方尾
> = ∑'_{i∉t}κᵢ² 经张量 Parseval + tail_indicator_tendsto_zero)、
> 第 4 节(cycle2/塔比较组装,消费 hsNorm_compPowR_sub_le)、第 5 节(A4 的
> B 侧极限 ‖B−B_t‖→0 + 对角 ℓ² 内容 = A7 尾)、第 6 节(最终组装
> diagSum_Bop_eq_weightedCycle ∀k≥2 + exists_weightedRieszSpectrum_min +
> equivalentKernel r 实例化)。
> **M1 验收仍未通过**(诚实口径)。
> v4.31 雷区本轮新增(累积):`Finset.sum_le_sum_of_subset` 需
> CanonicallyOrderedAdd(ℝ 无,ENNReal 运输绕行);`Set.mem_compl_iff` 的
> dot-notation `.mpr` 有时失效(用 `(Set.mem_compl_iff s x).mpr` 全参形式);
> `Set.indicator_nonneg (∀ a ∈ s, 0 ≤ f a) i` 直接给非负性;`tendsto_const_nhdf`
> 不存在(是 `tendsto_const_nhds`,Tendsto.sub 后需 `rw [sub_zero]` 消目标);
> `Filter.Tendsto.congr' h (tendsto)` 是函数形式非 iff;`Finset.sum_insert`
> 在积分 binder 下 rw 失败(改 `simp only`);`integral_prod_mul (f) (g)` 本版
> **无可积性假设**;`MemLp.mul (hf : MemLp f q) (hφ : MemLp φ p)` 结论是
> `MemLp (φ * f) r`(乘积顺序!);`Finset.sum_filter (p) (f)` 方向 =
> filter-和 → ite-和;`Integrable.comp_fst` 需显式 ν + IsFiniteMeasure(改用
> `Integrable.op_fst_snd (by fun_prop) ⟨1, ...⟩`);定义在 binder 下的
> `rw [def名]` 失败(改 `show`/defeq 展开);`tendsto_congr'` 未知
> (`Filter.Tendsto.congr'`);`specOperator` 的系数族 `{c}` 是**隐式**参数
——def/have/rw 钉参处必须 `(c := …)` 命名传参(位置传参被当成 hc,报
Application type mismatch);无 `DecidableEq ι` 的 `Type` 上 `if i ∈ t` 不可
判定——节级 `open scoped Classical` 统一 def 与引理 show-ite 的实例;
rw 的 rfl-probe 常已自动收尾,显式补 `rfl` 可能报 No goals to be solved
(报错再删);/tmp 里 import 本文件的公理审计前必须先 `lake build` 刷新
olean(否则 Unknown constant);`ENNReal.ofReal_tsum_of_nonneg` 本版带**两个参数**
(非负 + Summable);refine 链中 by-block 遇到含 ?b 的目标时 rw 的 auto-rfl 会把
?b 赋值吞掉目标(要 show 类型钉死);`•` 优先级高于 `*`,`c i * ⟪v i,x⟫ • v i`
会被解析成 ℝ×L2 混乘(必须 `(c i * ⟪v i,x⟫) • v i`);`ℝ≥0∞` 记法需
`open scoped ENNReal`(本文件头未开);`← ENNReal.ofReal_mul` 带显式证明参数
会把模式钉死(改 `exact (…).symm`);binder 下的 `rw [Finset.sum_insert]`
不稳定(改 show-项 + tsum_congr);`sum_inner`/`inner_sum` 分工:前者和在
第一个参数,后者和在第二个参数;`X ^ n y` 解析为
`X ^ (n y)`——幂后跟应用参数必须整体括号 `(X ^ n) y`(声明与引理皆然);
`ContinuousLinearMap.map_sum` 本版不存在(map_sum 与 Measure 二义,用
`_root_.map_sum`);长复合项用 `set … with h` 缩写 + 各引理证明内 `rw [h]`
展开;real_inner_comm 在 rw 列表中方向不稳(exact real_inner_comm _ _ 或
hstep 显式等式链更稳)。

## 上一轮交接状态(2026-09-22 置顶块,留档)

> 交接状态(2026-09-23 更新):**最新接手任务书 =
> `HANDOVER_PROMPT_session4_takeover4.md`**(含 k=2 闭环路线与一般 k 截断路线
> 的完整战术);旧 takeover3 版已被消费,留档。**原缺口①(B 紧性)已关闭**
> (c0a72c7 `Hurst/BopCompactness.lean` + b8eac1b
> `exists_Briesz_spectral_enumeration`:模型 B 带乘性精确、平方可和的谱枚举,
> 幂对角 HasSum 到 ∑'val^k,∀k≥2)。**唯一剩余缺口 = 压缩恒等式
> Diag_k(B) = Diag_k((WK)^k)**(截断构造+收敛 (a)(b);(c)=A4 已落地;
> 核侧恒等式已无 hconst 落地)。落地该恒等式后与
> `exists_Briesz_spectral_enumeration` + `diagSum_TOpRiesz_pow_eq_weightedCycle`
> 合成即得 `exists_weightedRieszSpectrum_min`,M1 验收复审。
> **第二轮增量**(18c9aa7,检查点 2026-09-22-2016-Compression-prelims):压缩
> 恒等式的 step-0 前置件已落地——`prod_sqrt_cycle_eq`(循环 telescoping,使
> B 侧/(WK) 侧循环项逐点相等的杠杆)+ `diag2_symmetric_eq_sumSq`(k=2 对称
> 坍缩 ⟪B²x,x⟫=‖Bx‖²)。

## 当前里程碑:M1(消除 hconst)— **任务 1/2/3 完成(诚实口径:M1 验收未通过,缺口已登记)**

- **本轮 landed(全部 exit=0、零 sorry、公理 ⊆ 三条、检查点+提交齐全)**:
  1. **A4 收尾**(d1a2f37):`diag_pow_sub_diag_pow_le` 全绿;文件头重写对齐实际声明。
  2. **M1-D2 核侧无 hconst**(ff550a3):`diagSum_TOpRiesz_pow_eq_weightedCycle`
     —— ∀k≥2 ∀Hilbert 基:加权核算子 `TOp(rieszKernel psi c omega)` 的幂对角和
     = `weightedRieszCycleIntegral k psi c omega`(可和性+恒等式)。旧
     `rieszSpectrumVal_hGen` 线在此处消费 hconst 的环节被直接替换。配套:
     `rieszKernel_section_sq_col`/`rieszKernel_sectionBounds_nohconst`/
     `hP_rieszKernel_nohconst`(截面界六件套去 hconst)。
  3. **M1-D2 B 侧 + 实例化**(b2007ec):`exists_Briesz_selfAdjoint_A7`
     (模型 B 全套结构包:自伴+√(κᵢκⱼ) 矩阵公式+A7 界 hTHS 形)+
     `diagSum_TOpRiesz_pow_eq_weightedCycle_equiv` +
     `exists_Briesz_selfAdjoint_A7_equiv`(ω := equivalentKernel r,模型侧
     前提全消解,**无 hconst**)。
  4. **验收机械件**(b3119f7):AxiomAudit 追加 35 行(0 error、公理干净)、
     `verification/build.log` 绿(9198 jobs)、check_coverage 27/27、
     verify_axioms 全过(sorryAx false/custom_axioms false);旧线注记
     (CapstoneV3Closed/GeneralKHasSumFinal 头部:hconst 不可满足,实际模型走
     EquivalentKernelSpectrum 线);规范 §5 声明式回写(A4 偏差 + D2 部分落地)。
- **not-landed(诚实登记,完成前不算 M1 验收通过)**:
  ① **B 紧性**(sqrtOp 有限秩截断论证;`hBridge_clm` 消费需要);
  ② **压缩恒等式 Diag_k(B) = Diag_k((WK)^k)**(A8–A9 路线 step0–3 的截断构造与
  三项收敛 (a)(b);(c)=A4 已落地);
  ③ 因此 `diagSum_B_eq_weightedCycle` 与 `exists_weightedRieszSpectrum_min`
  **未产出**(纪律:不得把待证目标包装为前提),**M1 验收(契约 §6)未通过**。
- **conditional/unconditional 分列**:本轮全部交付为 unconditional(相对其声明
  前提;capstone Riesz 数据 hpow/hg 与可行窗口 0<ψ、2ψ<1 为数据前提,与旧线同);
  conditional 件 = 旧线 rieszSpectrumVal_*/CapstoneV3Closed(已注记)。
- **编译证据**:/tmp 快照对应各检查点目录内完整日志(内嵌 exit=0):
  `2026-09-22-1423-A4`、`2026-09-22-1447-D2-kernelside`、
  `2026-09-22-1454-D2-Bside-instantiation`;全量 build=`verification/build.log`。
- **下一步(按 TRANSITION §10.4)**:①B 紧性(sqrtOp 截断;消费
  `isCompactOperator_of_tendsto` + 有限维靶紧性);②压缩恒等式(截断族
  K_N/B_N′ + A8 有限矩阵恒等式 + A4 已落地件);③之后 M1 验收复审;④阻断 2/3/4。
- **mathlib v4.31 雷区清单**见 TRANSITION_session4 §10.5(本轮新增:
  ring 不关 ≤ 目标;项级 fun u => by 隐参合成坑;Measurable.pow 指数是可测
  函数非数值;私有助手跨文件不可见须本地复刻;set 折叠后隐参须显式命名传参)。
---

## 历史块:Session-4 接管执行记录(2026-09-21 17:12–20:1x)

### 当前里程碑:M1(消除 hconst)— A/B 双落,三路并行在途

- **M1-A LANDED**(commit e4d79d8):`Hurst/UnweightedRieszOperator.lean` exit=0、
  零 sorry、公理审计 6 关键定理仅依赖 {propext, Classical.choice, Quot.sound}。
  检查点 `verification/checkpoints/2026-09-21-1827-M1A/`(源码+全量日志+sha256)。
  冻结 §2 接口全齐:def/symm/HS/compact/symmetric + A5 正性
  (`inner_TOp_unweightedRiesz_nonneg`,Γ–Laplace × exp-PSD 混合,Schur 可积性
  `integrable_laplace_integrand` 在 A 内消解)+ `exists_nonneg_eigenfamily`
  (κ≥0 + Summable κ²)。声明偏差:正性两定理带 `hc : 0 ≤ c`(契约更正 1,可满足)。
- **M1-B 现有内容 LANDED**(同 commit):`Hurst/PositiveSquareRoot.lean` exit=0、
  零 sorry、公理审计 5 关键定理三条基础公理。检查点
  `verification/checkpoints/2026-09-21-1832-M1B/`。已齐:mulOperator 层
  (hm+hess/action/symm/norm)、sqrtOp 层(S²=T/symm/nonneg/norm,
  `exists_positive_sqrt` 带附加 ‖S v i‖=√κ i 合取,真,加法性偏差)、
  A7 核心 `summable_and_bound_matrix`(族 Σκ_iκ_j⟪v_j,W v_i⟫² ≤ MR²∑κ²,自伴 W)。
  **未齐**:`exists_B_selfAdjoint_hs`(B=S∘M∘S 绑定+矩阵公式+任意基 A7 界)
  ——已派发 B2 agent(独占该文件)。
- **重要历史更正**:2026-09-18 13:45/14:18 两个中间态的错误清单**不可信**
  (tactic 中止/超时掩盖大量未编译段:hsplit2 未定义、ν 未定义、hHrow 族错误、
  结论合取未拆等十余处)。本轮全部以新鲜重编译逐轮收敛,A 重写 5 个块、
  B 重写 4 个块;13:45 "曾全绿" 的 A 正性块说法与现状无法互证,以本轮为准。
- **并行在途(18:3x 派发,3 路,文件互斥)**:
  1. B2:exists_B_selfAdjoint_hs(独占 PositiveSquareRoot.lean 追加);
  2. D2-pre:ι 可数化(新文件 Hurst/CountableEigenfamily.lean,含 SeparableSpace L2);
  3. D2-pre:A4 型幂对角扰动估计(新文件 Hurst/TracePerturbationEstimate.lean,
     HS 型前提形态对照 hTHS 声明)。
- 下一步:B2 落地 ⇒ 派发 D2 主组装(`Hurst/EquivalentKernelSpectrum.lean`,
  A8–A9 压缩路线,ω := equivalentKernel r 实例化)⇒ M1 验收
  (聚合 import + lake build + AxiomAudit 追加 + check_coverage/verify_axioms)。
- M1 后(契约 §1 顺序):阻断 2(FullChainEndpoint eventualCard)→ 阻断 3(P5
  归一化能量 W8–W9)→ 阻断 4(一般带符号 23:B–D)→ 端点组装。

---

# 历史块(2026-09-18 validation 轮)

更新:2026-09-18(独立 validation 轮启动)。

## 13:38 定时短查执行记录

- 三路诊断已分发(附"先重编译对照快照"提醒):
  - A:正性块三处(595 全函数传递而非逐点、608 `Submodule.span` 显式命名、Tonelli/ENNReal 逐块);基础层(含 `integrable_abs_sub_rpow_vol2`)确认绿。
  - B:级数块四项(451 Bessel≠Summable,应传 `summable_inner_sq_orth` 系;424 `mul_le_mul_of_nonneg_right`;rpow(1/2) 先转 sqrt;464 `mul_assoc`);乘法算子块先验收。
  - C:770 heartbeat **拆解慢项,不许全文件放大预算**;1171 纤维求和、1245 括号+|μ|^j 匹配。
- **编译证据纪律(全员,C 点名)**:`… | head -30` 的 `$?` 是 head 的退出码且截断日志;
  验收必须全量重定向 + 真实退出码。管道 exit-0 不计编译绿。
- **用语更正**:`hg`(= `integrable_abs_sub_rpow_vol2`)是 0≤s<1 内**可消解的内部可积性
  前提**,已消解;与 hconst 的"不可能性"是两类陈述,不得混用。
- **M1-D 精确接口已写入规范 §5**;二轮复核后路线定为 **A8–A9 有限谱压缩 + 极限**
  ("循环性移 S"作废:S=√K 一般非 HS;详见规范更正记录 7)。
  分工:M1-D1(tracePair_cyclic,抽象命题仍真,已派发但**角色降级为可复用工具**);
  M1-D2(diagSum_B_eq_weightedCycle + exists_weightedRieszSpectrum_min,依赖 A/B/C)。
  已登记缺口(压缩路线):ι 可数化(可分性)、A4 型幂对角扰动估计、A8 有限矩阵迹恒等式、
  三项收敛、`Summable (val²)` 推导、equivalentKernel 实例化——完成前不算 M1 验收通过。
- 13:xx 追加指令:C 逐声明计时定位 elaboration 慢点(禁全文件预算放大);
  A/B 先保存可编译小块再推进(正性/平方根/B+A7)。规范 §5 开头旧路线残留已清除。

## 各路检查点(2026-09-18 13:02 协调短查后更新;快照诊断已分发)

三路文件均已落盘且活跃(A 16KB/B 16KB/C 33KB,13:06-13:07 仍在编辑)。协调 agent 的
/tmp 快照诊断已逐条分发给各路(附"快照可能滞后,先重编译对照"提醒):

| 路 | 快照诊断 | 当前状态 | 剩余 M1 对象 |
|---|---|---|---|
| M1-A | 18 项:重点 = 可测性引理的局部路线错误(已修:复用已落地 `HS.measurable_abs_sub_rpow`,一行);API 项处理中 | ✅ **13:2x 检查点绿**:def+symm+可测+HS+对称⇒自伴(无权重前提)+紧性,全编译通过(exit 0);**额外交付:`integrable_abs_sub_rpow_vol2` 无条件消解旧 capstone 的 `hg` 前提** | 正性块(A5 Laplace+hc)进行中:`kernelPSD_rpow_dist_of_poisson`(用已落地 `laplace_rpow_neg` + `kernelPSD_exp_dist`)→ `inner_TOp_unweightedRiesz_nonneg` → `exists_nonneg_eigenfamily` |
| M1-B | 11 项:mpair 系列 `omega` 隐参误作首显参(改 `(omega := omega)`);`inner_mulOperator'` 非 definitional 不能 rfl(由 `inner_mulOperator` + mpair def 推) | hm+hess 双前提 ✔(协调已确认);正平方根与真实 B=S∘M∘S 尚未交付 | `exists_positive_sqrt` + B(定义等式绑定)+ A7 界 |
| M1-C(优先) | 仅 4 项:553/556 `real_inner_comm` 方向反;591 `tsum_le_tsum` 未知名(mathlib v4.31 改名);594 Finset 双和→subtype tsum 重写形状(先显式证明 `Finset.sum = subtype tsum`) | 33KB,该区域正在重写中 | 最终公开 `hBridge_clm`(含 hTHS + `Summable val²` 结论) |

主 agent 行动:①三份诊断已带"快照滞后"提醒分发;②C 为优先收敛路,已承诺:若
`real_inner_comm` 方向反复超过 ~2 次,agent 上报 `trace_state` 目标原文,主 agent 直接
给修正项;③不重跑全库;④M1 验收口径不变(不得以文件长度或去 sorry 计完成)。

## 各路检查点(2026-09-18 12:31 协调短查后采集)

| 路 | 文件路径 | 状态 | 最小编译检查点 | 当前 blocker |
|---|---|---|---|---|
| M1-A | `Hurst/UnweightedRieszOperator.lean` | **未落盘**(探索中;hc 修正已确认,正性路线用已落地 `laplace_rpow_neg`) | 无 | 已收到"尽早落地小块"指令:先 def/symm/可测/HS/对称⇒自伴,编译绿后再做紧性与正性 |
| M1-B | `Hurst/PositiveSquareRoot.lean` | **未落盘**(探索中) | 无 | 已收到修正 #2(可测+本质有界**双**前提;仅 hess 不够)+ 同款流程指令:先 mulOperator/action/范数/equivalentKernel 适用性推论 |
| M1-C | `Hurst/EndLevelTraceBridge.lean` | 落盘中(8.5KB,160 行级草稿,含 sorry/语法占位) | 尚未通过;最近编译错误:1×`unexpected token 'else'`(语法)+ 2×`unsolved goals` | 语法占位消除后进入证明填充;HS 型条件修正已传达 |

协调指令执行:①M1-B 可测性遗漏已发(签名需 `hm : Measurable omega` + `hess` 双前提,
实际 equivalentKernel 上消解;规范 §3 已同步);②A/B 收到"先落小块、报最小编译检查点、
长期卡住要报错误原文"的流程指令;③不重跑全库构建。

## ⚠️ 证据事件更正(2026-09-18 14:1x,独立复核发现)

13:45 检查点所用 /tmp 日志路径与各路 agent 的自用编译路径**撞车被覆盖**
(现行文件内容为 A_EXIT:1 / C_EXIT:1,系 agent 中间态的后续编译)。原检查点的
Lean 真实退出码(A_EXIT:0 / C_EXIT:0)仍保留于会话 exec 标准输出,已复制存档:
`verification/checkpoints/2026-09-18-1345-incident/`(含 README)。但**该保留证据
仅为退出码文本,不足以独立复现历史结果**——历史声明据此降级为"曾有 exit-0 记录,
完整日志已失"。
**流程修正(即日起)**:每个通过检查点 = 专属目录
`verification/checkpoints/<日期时刻>-<track>/` 内绑定 {源码快照 .lean, 完整编译日志
.log, 日志内嵌真实退出码 exit=…, sha256.txt},四件齐备才计通过。
14:18 快照轮(源码快照已存 `verification/checkpoints/2026-09-18-1418/`,逐文件
全量编译 + hash)结果将回填下表。

## 17:1x:A8 最终落地(已提交 e05b356)

`Hurst/FiniteMatrixTraceCycle.lean`(纯 Mathlib,无 sorry)**全绿落地**:exit=0 全量日志、
olean 已产出、公理仅基础三条;检查点 `verification/checkpoints/2026-09-18-1714-A8/`
(hash 自仓库根校验 2/2 OK,协议格式与 M1D1 略异——仓内相对路径,后续统一为目录内裸名)。
交付(A8 = M1-D2 压缩路线的有限维核心):
- `trace_pow_eq_cycleSum`:一般矩阵幂的迹 = 循环乘积和(`Fin (k+1)` 循环编码 k≥1,
  声明偏差:k=0 字面情形为假);
- `trace_Bm_eq_cycleSum`:√ 结构 B-矩阵的迹 = κ-加权循环和(√-伸缩相消需 `κ ≥ 0`);
- `trace_WKm_eq_cycleSum`:WK-矩阵同循环和(无需符号条件)。
**M1-D 依赖项 A8 ✔**;C ✔。剩余:A 收敛、B 的 S/B/A7 → M1-D2 派发。

## 15:2x:M1-C 最终落地(已提交 fcc2822)

`Hurst/EndLevelTraceBridge.lean`(1291 行)**全绿落地**:全量日志 exit=0(0 字节日志)、
olean 已产出、`#print axioms` 仅基础三条。交付:
- `exists_diag_enumeration_clm`:抽象紧自伴 CLM 的对角枚举 + 多重性 + `|val j| ≤ ‖T‖`
  (声明的偏差:一般紧 T 无法给出可和性,消费方从 `hBridge_clm` 的结论推导);
- `hBridge_clm`:hTHS 基一致矩阵平方和假设(M1-B 的 A7 交付)+ **`Summable (val²)`
  作为结论** + HasSum 形式(junk-tsum 依赖已消除);
- `hBridge_clm_tsum`(tsum 形式推论)+ 新胶水 `summable_kappaSq_of_matrixSq`
  (hTHS ⇒ `Summable κ²`,private)——**正是 M1-D 压缩路线的消费件**。
逐声明耗时:max 10.3s(hBridge_clm),仅两处**局部** maxHeartbeats 注释(文件预算不变)。
检查点:`verification/checkpoints/2026-09-18-1520-M1C/`(四件齐备)。
**M1-D 依赖项 C ✔**;A(收敛中)/B(S、B、A7 进行中)/A8(进行中)落地后即派 M1-D2。

## 验收级编译检查点(2026-09-18 13:45,**证据降级**,见上)

方法:`lake env lean <file> > /tmp/hurst-main-1345-<track>.log 2>&1`,退出码取自 Lean 本身
(无 head 管道)。检查点 = 该时刻的快照证据;各路 agent 随后仍在编辑,最终验收以
completion report 后的新鲜全量编译 + axiom 检查为准。

| 路 | 检查点退出码 | 日志路径 | 该时刻已编译通过的具体定理 | 当前 blocker |
|---|---|---|---|---|
| M1-A | **exit 0** | `/tmp/hurst-main-1345-UnweightedRieszOperator.log` | 全部 36 项声明,含冻结接口 `hsKernel_unweightedRieszKernel`/`isSymmetric_TOp_unweightedRiesz`/`isCompactOperator_TOp_unweightedRiesz` 与 **hc 版正性块** `inner_TOp_unweightedRiesz_nonneg`、`exists_nonneg_eigenfamily`;另有 `integrable_abs_sub_rpow_vol2`(hg 消解)、`lintegral_laplace_eq`、`lintegral_schur_dir(_swap)`、`integrable_laplace_integrand` | 检查点后 agent 仍编辑(14:0x 中间态 olean 构建未过=正常迭代);待 completion report 后重验 + axiom |
| M1-B | exit 1(剩 2 错) | `/tmp/hurst-main-1345-PositiveSquareRoot.log` | 已绿小块:`mpair` 层(线性/对称/界)、`mulOperator`+`_apply`+`inner_mulOperator(')`+`_symm`+`norm_le`+`_action`、`measurable_equivalentKernel`+`aeBounded_equivalentKernel`(实际模型适用性)、`specPair`/`summable_specPair` 可和层 | 464:xx unsolved goals、471 case tag `hf`(协调 4 项已在消);**尚未写出** `exists_positive_sqrt` 与 B=S∘M∘S 绑定构造 |
| M1-C | **exit 0** | `/tmp/hurst-main-1345-EndLevelTraceBridge.log` | 全链 48 项声明,含 **`exists_diag_enumeration_clm`、`hBridge_clm`、`hBridge_clm_tsum`、`summable_val_of_summable_kappa`**(End 级桥完整交付)及支撑(纤维分组、|μ|≤‖T‖、可数枚举) | 检查点后 agent 扩展至 76KB(14:12 中间态构建红=正常迭代);待 completion report 后重验 + axiom |

第四路 **M1-D1**(`Hurst/TracePairCycle.lean`,`tracePair_cyclic`,抽象配对循环性,
不依赖 A/B/C)已于 13:5x 派发。

## 下一步接口(M1-D,已冻结于规范 §5)

- M1-D1:`tracePair_cyclic`(进行中)。
- M1-D2:`mulOperator_comp_TOp`(左乘=核运算)→ `diagSum_B_eq_weightedCycle`
  (step1 算子恒等式 → step2 循环性 → step3 核化 → step4 k 步迭代 → step5 加权认同)
  → `exists_weightedRieszSpectrum_min`(组装 + equivalentKernel r 实例化)。
- 依赖:A 的 `exists_nonneg_eigenfamily`(✔ 检查点绿)+ B 的 S/B 绑定(进行中)+
  C 的 `hBridge_clm`/`exists_diag_enumeration_clm`(✔ 检查点绿)。

## 14:18 快照轮结果(源码快照+完整日志+内嵌退出码+sha256 已绑定)

存档:`verification/checkpoints/2026-09-18-1418/`(sha256 校验 OK)。**14:18 时刻三路
均为中间态、均未绿**(与 13:45 的 A/C exit-0 检查点相比是 agent 后续开发引入的新中间态):

| 路 | exit | 首个错误 | 诊断 |
|---|---|---|---|
| A | 1(5 错) | 387:63 unknown identifier `y` | 变量作用域(收正性块时引入) |
| B | 1(4 错) | 613:6 rewrite 失败 | specPair/可和层收尾 |
| C | 1(7 错) | 773:65 `set_option` 语法位置 | heartbeat 拆解中的语法错 |

**14:5x**:D1(`tracePair_cyclic`)完成并按协议归档
`verification/checkpoints/2026-09-18-1500-M1D1/`(exit=0,快照+日志+hash 齐备);
D1 执行者已转做 **A8 有限矩阵迹恒等式**(新文件 `Hurst/FiniteMatrixTraceCycle.lean`,
纯有限维,无 S/B 依赖)。A/B/C 已被要求各自报告:当前最小失败目标、逐声明耗时、
现有绿色小块清单;收敛优先于推进 S²=K / B=S∘M∘S / A7。

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
