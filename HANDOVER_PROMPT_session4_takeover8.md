# Session-4 接管任务书(takeover8):统计闭环第一步——hane 谱式消解 → hband 中心带消解 → hBias 立项定界

## 0. 环境与对象

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `4bce44f`,提交链见 §1)。
- 里程碑状态:takeover7 已完成并落地(commit `93c60b2` formal / `4bce44f` docs;
  检查点 `verification/checkpoints/2026-10-05-2256-FeasibleRates-scalar-rates/`)。
  **主线端点为 `Hurst/FeasibleRates.lean:453`
  `actualQ1_knownScaleH_fullChain_generalSigned_feasible`**(γ = f t 可行实例,
  标量率已实例化,β-窗口 `0 < β < (1−f t)(4 f t−3)`)。
  **既得成果不得回退**:阻断 1–4 关闭、归一化能量线、一般符号线、端点组装、
  标量率实例化全部落地;hconst 线条件文件照旧不碰。
- 本轮里程碑:任务 1(hane 谱式消解)→ 任务 2(hband 中心带消解)→
  任务 3(hBias 立项定界)。顺序执行,小步优先。
- 当前状态一句话:端点 conditional 仅余三个数据前提——hane(特征行非退化)、
  hband(中心带)、hBias(E5 偏差包络),加上模型窗口/b-带/β-窗口等真数据;
  聚合验收基线 = 全量 `lake build Hurst` 9214 jobs 绿、AxiomAudit 2549 行全 ⊆
  {propext, Classical.choice, Quot.sound}、零 sorry。工作区应干净
  (仅协调员的 `ZCODE_VALIDATION_MONITOR.md`,勿碰)。

## 1. 已落地快照(takeover7 全景;全部 exit=0、零 sorry、公理 ⊆ 三公理)

- `Hurst/FeasibleRates.lean`(516 行,6 公开定理):
  `feasibleR_nat_tendsto`/`feasibleR_tendsto_atTop`(:84/:96,R n = ⌊n^β⌋₊ → ∞)、
  `feasibleR_cut_tendsto`(:127,切割率,β-窗口 `β < (1−γ)(1−2ψ)`)、
  `feasibleR_env_tendsto`(:213,尾包络五项逐项消解,对一切固定实常数成立——
  强于端点的 ∀≥0 形状)、
  `…_generalSigned_scalarRates`(:390,主端点 hR/hcut/hEnv ⇒ β-窗口)、
  `…_generalSigned_feasible`(:453,γ = f t;hgrid ⇐ b-带 `(1−f t)² < 1−b`,
  hE5 ⇐ hlong 纯算术,镜像 FullChainEndpoint:432)。
- 任务 3 分类定稿(takeover7):hane = M1 特征行非退化数据前提;
  hband = file-22-W9 中心校准数据前提;hBias = E5 偏差侧数据前提
  (机械指针 E5RateLink:123/:300,消解需新里程碑,不弱化换绿)。
- 文档回写:VALIDATION_PROGRESS 置顶块(2026-10-05 takeover7,含 9 条 v4.32
  雷区批)、TRANSITION §0、backlog.md 状态注记(B01–B10 未动)。

## 2. 必读文档与顺序

1. `VALIDATION_PROGRESS.md` 置顶块(2026-10-05 takeover7):落地表、雷区累积表
   (先读;§5 只是摘录)。
2. 消费面代码(逐行核对,行号已验证):
   - 端点前提列:`Hurst/FeasibleRates.lean` — 定理 :453,hbband :459,
     **hane :460**,β :463,**hband :465**,**hBias :474**;
   - hane 的恒等式骨架:`Hurst/FirstStrideGrid.lean:24`
     `gridStrideFirst_feature_identity`(系数行作用和 =
     `(d/n)^(H left) • gridStrideFirstActual`,d=1;正标量 ≠ 0)
     ⇒ hane ⟺ `gridStrideFirstActual n 1 H i ≠ 0`;
   - 谱机械:`Hurst/Harmonizable.lean` — def :176、inner :183、
     **inner_formula :248**、norm_sq :288、inner_same :314、
     increment_norm_sq :323;`Hurst/VaryingIncrement.lean` —
     def normalizedVaryingIncrement :13、frozen norm = 1 :19–29、
     uniform_remainder :37(varying−frozen ≤ C·B·ℓ^{1−b});
   - hband 的期望公式:`Hurst/GaussianLog.lean:153`
     `gaussianLogStatistic_expectation`
     (`E Ĝ(w,a) = ∑ w j (log ‖∑ a ji v i‖² + gaussianLogSquareMean)`;
     `gaussianLogSquareMean` 定义在 :82)、
     `Hurst/GaussianLogCovariance.lean:10`(gaussianLogSquareVariance);
   - 单位权和:文件头注明 `p5KnownScaleLogStatistic` 用"unit-sum local weights
     `w = S⁻¹ u`"(P5LogHLayers.lean:78–82);∑w=1 的引理自行 grep
     (`localPolynomialWeights`/`observationDifferenceWeights` 附近)。
3. `TRANSITION_session4_2026-09-21.md` §0(2026-10-05 takeover7 快照)与 §3/§4。
4. E5/hBias 方向(任务 3):`Hurst/E5RateLink.lean:123`(correlationEnergy_rate)、
   :300(e5_fluctuation_rate_of_window,L1 波动率 ≤ F·n^{-γ});
   旧消费链 `E5ChainInstantiation` → `P5TruthCenter.p5_truthCenter_drift_s1`。

## 3. 任务序列(按序;小步优先,每步独立落地)

任务 1 = hane 谱式消解(建议新文件 `Hurst/FeatureRowNondegenerate.lean`):
目标定理:`∀ n H i, gridStrideFirstActual n 1 H i ≠ 0`(对任意 H : Fin n → Ioo 0 1,
不经 Holder/中点采样假设,比端点的 hane 更强、可直接回灌)。
主路线 A(∀ n,应可全量证):
`gridStrideFirstActual = ℓ^{−h} • (F_k(s+ℓ) − F_h s)`,h = H(left),k = H(right),
s = grid n i,ℓ = 1/n > 0。范数平方用 Harmonizable :288/:248 展开为显式积分
(F 谱振幅 e^{isξ}|ξ|^{−·} 型);非零性归约为被积函数非 a.e. 零:
- 若 h = k:含 |e^{iℓξ} − 1| 因子,ℓ ∈ (0,1] 非零 ⟹ 不 a.e. 零;
- 若 h ≠ k:振幅比 |ξ|^{h−k} 在正测集上 ≠ 1 ⟹ 不 a.e. 零。
"非负可积函数 > 0 ⟹ 积分 > 0"取仓内先例风格(measure-positive)。
备用路线 B(仅 eventual,作交叉验证不作交付):VaryingIncrement.lean:37 的
uniform_remainder + frozen norm = 1 ⇒ 大 n 时 ‖varying‖ ≥ 1/2。
**诚实条款:若 A 在某 h,k 情形被证伪(存在反例),立即停手登记,
不得改用弱化陈述冒充;若 A 卡壳 >2 次同一错误,贴 trace_state 求助。**
落地后:把 scalarRates/feasible 两端点的 hane 前提删除(内部派生),
消解表与 VALIDATION_PROGRESS 同步登记。
任务 2 = hband 中心带消解(建议 `Hurst/CenterBandDischarge.lean`):
先用 GaussianLog.lean:153 把 hband 中的积分换成显式和
`∑ w j (log ‖组合向量‖² + gaussianLogSquareMean)`;组合向量的范数经
FirstStrideGrid.lean:24 恒等式 = `(1/n)^{H left} · ‖increment‖`,
frozen 增量范数 = 1(VaryingIncrement.lean:26),varying 余项有界 ⇒
手推草图(**待 Lean 验证,符号以实际证出者为准**):
`E Ĝ_unit ≈ ∑ w j (−2 H_j log n + O(1))`,若 ∑ w = 1 且 H_j → f t 一致,
则 `E Ĝ_unit = −2 f t log n + O(log n · sup|H_j − f t|) + O(1)`,
带比 `(cσ − E Ĝ_unit)/(2 log n) → f t ∈ (3/4, 1)` ⟹ 取 `d < 1 − f t`
(如 d := (1−f t)/2)与有界 cσ 即可 eventual 满足。
交付:显式 (cσ, d) 的 hband 消解定理 + 回灌端点;若 ∑w=1 或
H_j 一致性在仓内缺引理,先补小引理再组装;若草图某步被证伪,
如实登记并以证出的形状重述带条件。
任务 3 = hBias 立项定界(不强制消解):
注意端点要的是率 |E Ĝ_n − f t| ≤ C·n^{−γ},而任务 2 的自然展开只给
o(1)/(1/log n) 阶——**这是 E5 里程碑的实质内容,不得为凑绿弱化端点前提**。
交付:hBias 的分解蓝图(E Htilde = (cσ − E Ĝ_unit)/(2 log n) + 任务 2 渐近
+ 裁剪恒等 p5Trunc01_eq_self(P5LogHLayers.lean:69,带上条件时裁剪=恒等)),
写明"要达 n^{−γ} 率还需要哪些二阶展开",入 VALIDATION_PROGRESS 的
新里程碑条目;若任务 1/2 提前收官且余量充足,可动手做二阶展开的第一块。
任务 4(余量)= 零自由度实例 β := (1−γ)(4 f t − 3)/2(takeover7 可选未做项)、
expectation-centered/unknown-scale 变体镜像(旧 FullChainEndpoint 三变体格式)、
backlog/文档收尾。

## 4. 硬性纪律(违反须返工;与前几轮相同)

- 默认禁用 subagent:全部形式化亲自完成(仅当用户当轮明确授权时例外)。
- 落地前偏差自检:(a) 等式/不等式方向;(b) 前提真实消费,文档不超签名;
  (c) 新前提全量词域可满足(反例清单纪律);(d) 任务 1/2 的"更强定理回灌端点"
  必须逐处替换并声明,不做全局重写。
- 编译证据:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`;
  验收 ≠ 编译绿:公理 ⊆ 三公理 + 检查点四件套(源快照 + compile.log +
  axioms.log + sha256.txt,目录内裸名);/tmp 做公理审计前先 `lake build` 刷新
  olean;检查点时间戳用 `date` 实际输出;聚合时写 `verification/build.log`
  并追加 `verification/AxiomAudit.lean`。
- land-then-follow-through:新鲜编译 → 检查点 → git commit → 增量
  `lake build Hurst` → 回写 VALIDATION_PROGRESS 与 TRANSITION。
- 小步优先;同一声明卡 >2 次同一错误,贴 trace_state 原文求助。
- 不碰 `ZCODE_VALIDATION_MONITOR.md`;文档编辑用 python 字符串手术。

## 5. 雷区(累积版在 VALIDATION_PROGRESS 置顶块;takeover7 批 + 本轮相关摘录)

- `Tendsto.congr'` 方向(takeover7 勘误,以此为准):`hl : 已收敛函数 =ᶠ 目标函数`。
- `by linarith` 在有隐式元变量时失败:显式类型化中间 `have`;单乘积原子先 rewrite。
- `Real.rpow_neg` 需显式传指数;`const_mul` 极限是 `𝓝 (c*0)` 需 simpa 归一;
  `Function.comp_def` 处理裸复合;`eventually_atTop.1` 配具名 have 取见证。
- 复值内积/范数展开(Harmonizable 系)注意 `real_inner_self_eq_norm_sq` 只在
  实内积空间;ℂ-Lp 用 `L2.inner_def` + 积分号下再取实部;`Complex.exp`
  的 re/im 展开参考 Harmonizable.lean:198–210 的 simp 集。
- "积分 > 0"论证:先证被积函数在某正测集上 > 0,再套正性引理;不要试图
  对积分号直接 nlinarith。
- 其余(fun x => 逗号、HasSum.congr_fun、abel in L2、neg_pow 的 simp 自环、
  even_add_odd 显式 f 实例化等)见置顶块累积表。

## 6. 汇报要求(诚实条款)

landed / not-landed 分列;任务 1 若交付"更强定理"(∀ H 的非退化),须给出
端点 hane 删除处的逐点替换清单;任务 2 的 (cσ, d) 必须显式并附带比的极限计算;
任务 3 的蓝图不得把"率不够"粉饰为"机械步骤";hane/hband 未双双落地前,
不得宣称"端点无条件化";编译日志路径 + 真实 exit code + 公理审计输出原文。
