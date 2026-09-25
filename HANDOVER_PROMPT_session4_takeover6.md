# Session-4 接管任务书(takeover6):阻断 2(eventualCard 传播)→ 阻断 3(P5 归一化能量 W8–W9)→ 阻断 4(一般符号 23:B–D)→ 端点组装

## 0. 环境与对象

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `c2f6282`,提交链见 §1)。
- **里程碑状态:M1 已验收通过**(2026-09-24,commit `c2f6282`;合同 §6 四项全绿:
  全量 build 9201 jobs / AxiomAudit 0 真实错误 / check_coverage 27/27 /
  verify_axioms 全过;实例化 `exists_weightedRieszSpectrum_min_equiv`)。
  **hconst 阻断(阻断 1)在迹幂侧与谱侧均已消除,不得回退或重开。**
- 本轮里程碑:**阻断 2 → 阻断 3 → 阻断 4 → 端点组装**(顺序用户指定,不可跳序)。
- **当前状态一句话**:M1 线全部闭合且文档已回写(VALIDATION_PROGRESS 置顶块 /
  TRANSITION §0 快照 / spec §5 落地记录);剩余主线 = 三个下游不可满足/不充分
  前提的修复与最终端点组装。工作区应干净(仅协调员的未跟踪文件
  ZCODE_VALIDATION_MONITOR.md 可能有改动,勿碰)。

## 1. 已落地快照(M1 全景;全部 exit=0、零 sorry、公理 ⊆ {propext, Classical.choice, Quot.sound})

- M1-A/B/C/A8/D1/可数化/A4/B 紧性/B 谱枚举(历史提交 e4d79d8…b8eac1b,见
  TRANSITION §10.2)。
- k=2 压缩恒等式闭环(d628418,`Hurst/CompressionIdentity.lean`)。
- 一般 k 路线第 1/2a/2b/2c/3a/3b 节(85c05ae…8f910e4)。
- **第 4–6 节(接管者 4,2026-09-24)**:4a `7d0684f`(HS 平方尾 = κ²-尾 +
  level-set 耗竭 + 核尾→0)→ 4b+4c `5b5fbe8`(M_ω∘T_t = TOp(ω·truncKernel)
  + 加权差控制)→ 4d `1ea0961`(核侧幂对角收敛,cycle2/塔 Lipschitz 挤压)
  → 第 5 节 `23f1f67`(B 侧 A4 极限 14 定理:B−B_t 两项分解、对角 ℓ² 内容 =
  A7 族 t×t 补指示 → 0)→ 6a `bcfd3e3`(**`diagSum_Bop_eq_weightedCycle`**
  ∀k≥2)→ 6b `af11726`(**`exists_weightedRieszSpectrum_min`**)→
  6c `7bc1663`(**`exists_weightedRieszSpectrum_min_equiv`**,ω :=
  equivalentKernel r 实例化)。全部在 `Hurst/CompressionGeneralK.lean`
  (~3400 行),检查点 `verification/checkpoints/2026-09-24-*-CompressionGeneralK-s4a…s6c/`。
- 文档回写链:…→ c80d3d0 → c2f6282(M1 验收记录 + 雷区累积)。
- 条件线留档(勿删勿据其宣称完成):`rieszSpectrumVal_hGen`/`CapstoneV3Closed`/
  `GeneralKHasSumFinal` 等,头部均注明"hconst 不可满足,实际模型走
  EquivalentKernelSpectrum/Compression 线"。

## 2. 必读文档与顺序

1. `VALIDATION_PROGRESS.md` 置顶块(2026-09-24):M1 验收记录、第 4–6 节落地表、
   **v4.31 雷区总表(累积,先读;本任务书 §5 只是摘录)**。
2. `TRANSITION_session4_2026-09-21.md`:§0 最新快照、§3 过程纪律、§4 开发流程
   (4.2–4.3 已转主 agent 自律)。
3. `SESSION3_INDEPENDENT_REVIEW_2026-09-18.md` §1–§3:三个阻断的诊断原文与修复指引
   (阻断 2 = §1 表 + `Session3PremiseAudit`;阻断 3 = §2(未写成 Lean 矛盾定理);
   阻断 4 = §3)。
4. 修复方案原文:
   `direct_proofs/22_long_memory_repair_lean_handoff.md`(W6–W9;W8–W9 = 归一化
   能量 `S^(2ψ−2)·∑∑rho_ij² = O(1)` + 近/远带四阶 Hermite 余项 + log/clipping/
   中心化同步修正);
   `direct_proofs/23_spectral_probability_support.md`(B–D:正/负谱分别排序、
   有符号系数 ℓ² 收敛、二阶 Gaussian chaos 极限)。
5. 消费面代码(逐行核对,行号已验证):
   - `Hurst/FullChainEndpoint.lean`:三处端点 `hm`(行 158/318/382,均
     `∀ n, 0 < (localWeightActiveSet …).card`;382 处指数为 `-(f t)`)+
     行 174 `hE2`(未归一化 `∃ C, ∀ᶠ n in atTop, ∑∑ rho_ij² ≤ C`);
   - `Hurst/P3SignedMatching.lean`:行 178/429 `hNegMass`(负谱平方质量 → 0)
     + 文件内自注的 interleaved sorted row 分布认同缺口;
   - 修复先例:`Hurst/CapstoneV2.lean:347`
     `actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard`(D3 安全
     零填充模式;P2SpectrumV2.lean:224 / CapstoneV2.lean:603 消费);
   - 矛盾依据:`verification/Session3PremiseAudit.lean`
     (`session3_fullChain_all_rows_impossible` 行 11、
     `session3_equivalentKernel_hconst_impossible` 行 28,公理三条);
   - 数学事实:`Hurst/GaussianLogRisk.lean:10`(`featureCorrelation` 定义;
     对角 `featureCorrelation v a a = 1`)、`Hurst/OptimalActiveRowDensity.lean:139`
     (`localWeightActiveSet_card_tendsto_atTop`)。

## 3. 任务序列(按序;小步优先,每步独立落地)

### 任务 1 = 阻断 2:FullChainEndpoint 的 `hm : ∀ n, 0 < card` 传播为 eventual 形

- 矛盾(已 Lean 证明):`localWeightActiveSet 0 …` 为空,`∀ n` 版本在 n=0 假,
  见 `Session3PremiseAudit.session3_fullChain_all_rows_impossible`。
- 修法(先例 = CapstoneV2 的 D3 安全零填充):三处端点(158/318/382)把 `hm`
  改为 eventual 形(`∀ᶠ n in atTop, 0 < card`,或结论改为 `∃ N, ∀ n ≥ N`),
  并重审端点证明内所有 `hm` 消费点:空活跃集的行贡献为 0(对 `Fin 0` 求和
  = 0),极限结论通常逐字保留——逐个验证,不得默认。
- 新前提必须全量词域可满足(反例清单纪律:∀k hPair、∀r 塔界+单 E、hconst、
  现在的 ∀n card>0 都是不可满足打包的教训)。
- 落地后:`session3_fullChain_all_rows_impossible` 指向的旧形态已修复,在
  VALIDATION_PROGRESS 登记"阻断 2 关闭"(保留审计文件原样)。

### 任务 2 = 阻断 3:P5 能量前提按 22:W8–W9 归一化重做

- 不可满足性(直接数学推导,**尚未写成 Lean 矛盾定理**):在端点同要求的
  `hane` 下,`rho_ii = featureCorrelation v a a = 1`,故 ∑∑rho² ≥ 活跃点数,
  而 `localWeightActiveSet_card_tendsto_atTop` 使其发散。可选前置:把这个
  矛盾写成 Lean 定理(审计风格,入 `verification/`),按 M1 惯例归档。
- 修法(按 22:W8–W9):把 `hE2`(行 174)换成归一化能量
  `S^(2ψ−2) · ∑∑ rho_ij² = O(1)`(S 为带宽尺度;检查仓内已有的
  `S^(2ψ−2)` 标准化先例:`ActualKernelBandAsymptotics.lean:45`、
  `E5ChainInstantiation.lean:62/746`、`FrozenQuadratureInstance.lean:300`);
  结合近/远带证明四阶 Hermite 余项消失;**同步修正下游**(log、clipping、
  中心化)——不得只改 hE2 形状沿用原证明。
- 新前提可满足性:归一化形状须给出实际模型中的消解表条目(先数学后 Lean,
  回写契约式文档;参考 M1 的 §1 表格式)。

### 任务 3 = 阻断 4:一般带符号极限按 23:B–D

- 现状:`hNegMass → 0` 只覆盖负谱渐消;偶次幂剥 indisposes ±λ 的区分
  ("EvenPeeling 覆盖带符号区域"的说法已被复核否决)。
- 修法(按 23:B–D):正/负谱分别排序、有符号系数的 ℓ² 收敛、二阶 Gaussian
  chaos 的极限;同时处理 P3SignedMatching 文件内自注的 interleaved sorted
  row 分布认同缺口。
- 与阻断 2/3 的耦合:端点签名若在任务 1/2 中已改,这里以改后签名为准。

### 任务 4 = 端点组装

- 三阻断关闭后,把 FullChainEndpoint 的三处端点接到已消解前提上并聚合编译。
- 注意:M1 产出的新件(`diagSum_Bop_eq_weightedCycle`、
  `exists_weightedRieszSpectrum_min(_equiv)`)可供下游消费;旧的
  conditional 消费(`rieszSpectrumVal_*`、`CapstoneV3Closed`)如需替换为
  无 hconst 版,逐点替换并声明,不做全局重写。

### 任务 5(仅余量):`backlog.md` 清理与 TRANSITION 收尾。

## 4. 硬性纪律(违反须返工;与前几轮接管相同)

1. **停用 subagent**:全部形式化亲自完成,不委托。
2. **落地前偏差自检**:(a) 等式/不等式方向与三角不等式合法性;
   (b) 前提真实消费,文档不得超出签名;(c) 新前提全量词域可满足。
3. **编译证据**:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`
   (全量重定向 + 真实 exit code,禁止 `| head`);**验收 ≠ 编译绿**:
   公理审计 ⊆ {propext, Classical.choice, Quot.sound} + 检查点四件套
   (`verification/checkpoints/<date-time>-<track>/` 内含源码快照 + 完整
   compile.log + axioms.log + sha256.txt,sha256 用目录内裸名)。
   在 /tmp 里 import 本文件做公理审计前必须先 `lake build` 刷新 olean。
   检查点目录时间戳用 `date` 实际输出。全量 `lake build Hurst` 约 2 分钟
   (9201 jobs),聚合验收时写 `verification/build.log`。
4. **land-then-follow-through**:新鲜编译 → 检查点 → git commit →
   (若需则增量集成)`lake build Hurst` → 回写 VALIDATION_PROGRESS 与
   TRANSITION(协调 agent 每 30 分钟只读检查)。
5. **小步优先**;同一声明卡 >2 次同一错误,贴 trace_state 原文求助,
   不要闷头磨。
6. **不碰 ZCODE_VALIDATION_MONITOR.md**(协调员未跟踪文件)。
7. 文档编辑用 python 字符串手术(Edit 工具部分替换曾产生孤儿文本)。

## 5. v4.31 雷区(完整累积版在 VALIDATION_PROGRESS 置顶块;接管者 4 新增批摘录)

- **`fun x,` 逗号形式已废除**(报 unexpected token ',';必须 `fun x =>`)。
- `HasSum.congr` 已改名 **`HasSum.congr_fun`**(h : ∀ x, g x = f x,新 = 旧)。
- `abs_add` 根名不存在:三角不等式用 `(AbsoluteValue.add_le AbsoluteValue.abs) a b`;
  `Real.dist_eq`/`dist_eq` 都在,但 `Real.abs_add` 不存在。
- 目标在 L2 等非 ℝ 群里时 `ring`/`linarith` 都不适用,用 **`abel`**。
- `Orthonormal` 的字段是 `.1 = norm_eq_one`、`.2 = orthonormal'`(双参
  `inner ℝ (v i) (v j) = if i = j …` 需自拼)。
- 第二参减法用 `inner_sub_right`(第一参才是 `inner_sub_left`);CLM coe 与
  Lin coe 显示不一致时,用**项式包装**(∀ u w, inner ℝ (Z u) w = …)绕开。
- `pow_le_pow_left₀` 需非负首参;`ContinuousLinearMap.opNorm_le_bound` 的
  f 是**首显参**;`Summable.const_mul` 不存在,常乘可和性手工
  `summable_of_sum_le`(c 需显式命名传参)+ 有限和重排。
- **大上下文内复合算子 defeq 展开(Bop/BtruncOp 的范数)即使 1M 心跳也超时**
  ——提取为小上下文独立引理 + 逐点 opNorm 链
  (`ContinuousLinearMap.le_opNorm` 逐级 + `opNorm_le_bound` 收口),
  这是唯一稳定路线(6a 节实测)。
- `Set.Finite.mem_toFinset`;`Set.indicator_of_notMem` 需 f 实参;
  `Real.sq_sqrt` 实例化需显式非负前提;`Finset.notMem_empty`;
  `Finset` 笛卡尔积记号是 `×ˢ`(非 `.prod`,后者是乘法monoid求积)。
- `integral_add` 方向与直觉相反;`rw` 一次替换全部同名 ite 实例(分支
  重写要数实例数);`X ^ n y` 解析为 `X ^ (n y)`,幂后跟应用必须 `(X ^ n) y`;
  lambda 下的 `refine ⟨_, ?_⟩` 结构易碎,先 `intro` 再 `refine`。

## 6. 汇报要求(诚实条款)

- landed / not-landed 分列;conditional / unconditional 分列;
  新契约/新前提的"实际模型中如何消解"表必须先于形式化写出并回写;
  编译日志路径 + 真实 exit code + 公理审计输出原文;
  已知缺口如实登记,不得粉饰为"机械步骤";
  阻断 2/3/4 全部关闭并复审前,不得宣称端点组装完成。
