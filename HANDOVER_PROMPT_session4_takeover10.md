# Session-4 接管任务书(takeover10):最终组装——诚实率漂移引理 ⇒ 统计闭环端点

## 0. 环境与对象

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `457eeb6`,提交链见 §1)。
- 里程碑状态:takeover9 已完成并经两轮审计(含审计者自纠的二次勘误)。
  **全部原料已落地且经独立验证**;本轮是纯组装:把十二块已验证零件拧成
  最后一条漂移引理,接出统计闭环端点。**既得成果不得回退;不得重开已证伪
  的路线**(一阶/二阶窗口在 γ = f t 处均不可行,见 HBiasSecondOrder:230/:240)。
- 当前最强端点 = `Hurst/CenterBandDischarge.lean:717`(zeroDof):前提 = 模型窗口 +
  b-带 + cσ + (C, hBias)。**hBias(率 n^{−f t})按手推在变剖面模型下不可满足,
  该端点目前对常规模型类空真**——本轮任务就是用漂移路线替换它。
- 聚合验收基线 = `lake build Hurst` 9220 jobs 绿、AxiomAudit 整文件 exit=0 且
  2600 条全 ⊆ {propext, Classical.choice, Quot.sound}、零 sorry;工作区应干净
  (仅协调员的 `ZCODE_VALIDATION_MONITOR.md`,勿碰)。

## 1. 已落地快照(takeover9 + 审计;全部 exit=0、零 sorry、公理 ⊆ 三公理)

- **任务书 v9 目标率被证伪并诚实登记**:二阶可达率 = **n^{−(2−2b)}**
  (`Hurst/IncrementLogSecondOrder.lean:598` 主定理,精确恒等式
  2⟨inc, mismatch⟩ = ΛΦ(m) − Φ(h),无对数损失;网格推论 :707)。
- **二阶包络**:`Hurst/HBiasSecondOrder.lean:103`
  `knownScaleEstimator_bias_envelope_grid_secondOrder`(窗口 γ ≤ 2−2b,
  C = F + Cst + Clog·W/2);log 级界 :65;窗口审计 :230/:240。
- **截断转移(尾部型,关键工具)**:`Hurst/TruncationTransfer.lean:95`
  `truncationCorrection_le`:|E trunc(X) − E X| ≤ **V + ε**,
  V = 二阶矩界,ε = {d ≤ |X−m|} 的测度界(d = m 到 [0,1] 余集的距离);
  配套 `meas_ge_le_of_lintegral_pow`(:58,ℝ≥0∞ Markov)。
- **E5BiasExpansion(已集成)**:期望恒等式 :618、**漂移界 :752**
  (`p5KnownScaleHtilde_drift_bound`:前提 hn/hδ/hane/hw1/hWabs/hcontr/hlog/
  hcσ,结论 |E H̃ − f t| ≤ D + (|cσ−c₀| + W·E)/(2 log n) 型)、
  权收缩实例链 :329/:460、条件包络 :885。
- **方差率原料**:`Hurst/NormalizedLogVariance.lean:75`
  `gaussianLogStatistic_variance_of_normalizedEnergy`
  (Var[Ĝ_unit] ≤ (4·gLSV·U²·C)·S^{−2ψ});实际模型能量界
  `Hurst/NormalizedActualEnergy.lean:44`;u-界
  `Hurst/NormalizedActualRemainder:40`;相关同一
  `Hurst/FirstStrideActualRows.lean:9`。
- **带比**:`Hurst/CenterBandDischarge.lean:209`(E H̃/(2 log n) → f t,
  任意固定 cσ)⟹ eventual 带成员;端点 :675/:717。
- **hane 已消解**:`Hurst/FeatureRowNondegenerate.lean:682`(∀n 形)。
- **权重三合一(先例)**:`Hurst/LocalWeights.lean:56`(det/行界/绝对和/
  k=0 矩 ⟹ hw1);活跃重加 `Hurst/ActiveSetReindex.lean:26`。
- Hurst.lean 挂线:E5B :682、ILSO :686、TT :690、HB :694、FRN :677、CBD :678。
- 文档:VALIDATION_PROGRESS 置顶块(takeover9 + 两轮审计勘误,含 §3 的
  完整路线与 ⚠️ 陷阱警告)。

## 2. 数学路线(已在 VALIDATION_PROGRESS 形式登记;此处为执行版)

**目标**:truth-centered 端点只需要漂移
`drift(n) := 2·S^ψ·log n·|E Ĥ_n − f t| → 0`(S = n^{1−γ},γ = f t,ψ = 2−2f t),
**不需要** n^{−γ} 率的 hBias。分解 `E Ĥ − f t = [E H̃ − f t] + [E trunc(H̃) − E H̃]`:

- **第一项(确定性侧)**:E5B:752 给
  `|E H̃ − f t| ≤ D + (|cσ−c₀| + W·E)/(2 log n)`,cσ := c₀ = gaussianLogSquareMean
  钉死后 = `D + W·E/(2 log n)`,其中 D = Cst·δ^p(hcontr)、E = Clog·n^{−(2−2b)}(hlog)。
  漂移第一项 ≤ `2S^ψ log n·D + S^ψ·W·E`
  = `n^{2(1−ft)²}·log n·Cst·n^{−ftp}` + `n^{2(1−ft)²}·W·Clog·n^{−(2−2b)}`;
  前者指数 `2(1−ft)² − ft·p < 2(1−ft)² − 3/4 < 0`(p ≥ 1,自动);
  后者指数 `2(1−ft)² − (2−2b) < 0 ⟺ (1−ft)² < 1−b = hbband`。
- **第二项(随机侧,⚠️ 不得用 crude 界)**:crude 界
  `truncExpectation_le_fluctuation`(修正 ≤ sd)喂进漂移得 **O(1) 不收敛**
  (sd ~ n^{−2(1−ft)²}/(2 log n),被 S^ψ 恰好抵消)。**必须用尾部型**
  TT:95:取 m = E H̃(由 CBD:209 带比,eventual m ∈ [d′, 1−d′],d′ = (1−ft)/2,
  此即 hbandc 与 hcover 的 d),V := Var(H̃) = Var[Ĝ_unit]/(4 log²n) ≤
  `(4·gLSV·U²·C)·n^{−4(1−ft)²}/(4 log²n)`(任务 1 的方差率),
  ε := Chebyshev 尾 ≤ V/d′² ≤ `4V/(1−ft)²`。于是修正 ≤ V·(1 + 4/(1−ft)²),
  漂移第二项 ≤ `C·n^{2(1−ft)²}·log n·n^{−4(1−ft)²}/log²n =
  n^{−2(1−ft)²}·O(1/log n) → 0` **无条件成立**。
- **hδp 自动**:包络若使用,δ^p = n^{−ftp} ≤ n^{−(2−2b)} 因
  `ft·p ≥ ft > 3/4 > 1/2 > 2−2b`(b > 1/2)。
- **hw1/hWabs/hcontr/hlog 均 eventual 化**:稳定性包需要 N₀(r) ≤ S = n^{1−γ},
  S → ∞ ⟹ eventual;消费在 ∀ᶠ n 语句内逐 n 取用。

## 3. 任务序列(按序;小步优先,每步独立落地)

任务 1 = **单位方差率**(建议并入本轮闭合文件或 `Hurst/UnitVarianceRate.lean`):
`hurstHolder_q1_unitVariance_eventually_bounded`:
在模型窗口 + hlong 下,`∀ᶠ n, Var[p5KnownScaleLogStatistic f r n (δ n) t;
featureGaussian(…)] ≤ (4·gLSV·U²·C)·S^{−2ψ}`(U/C 来自 NormalizedActualRemainder:40
与 NormalizedActualEnergy:44 的存在量词;Var 换形状用 mse 引理,先例见
P5JoinInstantiation 的 hunfold/h2 模式;相关经 FirstStrideActualRows:9 换成
featureCorrelation 形)。
任务 2 = **诚实率漂移引理**(建议 `Hurst/HonestRateDrift.lean`):
`honestRate_drift_tendsto_zero`:模型窗口 + hbband + r ⟹
`Tendsto (fun n => seamScaleC f t (fun m => m^{−ft}) n *
  |E p5KnownScaleEstimator … − f t|) atTop (𝓝 0)`
(或等价的 |·| 无绝对值版,以端点消费形状为准)。组装 = 第一项(E5B:752,
cσ 钉死,前提 eventual 化)+ 第二项(TT:95 + 任务 1 + CBD:209 带成员 +
Chebyshev)。**逐项指数对表 §2,不得引入 crude sd 界**。
任务 3 = **最终端点**(建议 `Hurst/HonestRateClosure.lean`,新叶子文件,
import CBD + E5B + TT + ILSO + HB,无环):
`actualQ1_knownScaleH_fullChain_final`:前提 = **模型窗口
(p,a,b,M,hp,ha,hb,hab,hM,f,hf,hF,t,ht,hlong)+ hbband + r**,结论同 zeroDof
(∃ Q,IsWeightedRieszSecondChaosLaw ∧ TendstoInDistribution)。骨架镜像 CBD:717
(其内部已把 hane/hband/d/β 全部内部化),把 hE5/C/hBias 替换为任务 2 的漂移
(经 `p5_transport_truthCentered_of_drift` 的 L1 漂移口径——确定性漂移下
∫|…| = |c_n·(E Ĥ_n − f t)|,先例见 FullChainGeneralSigned 端点的 hint 段);
cσ := gaussianLogSquareMean 内部钉死。落地后:挂 import 到 Hurst.lean 尾部 +
**AxiomAudit 追加后整文件重编译至 exit=0**(takeover8 教训)+ 检查点四件套 +
文档回写(消解表终行:端点 conditional 于 模型窗口 + b-带;旧 hBias 端点标注
legacy-空真)。**在协调者复审前不得宣称"统计闭环已验收"。**
任务 4(余量,不阻塞)= expectation-centered / unknown-scale 变体镜像;
旧 hBias 形状不可满足性的形式化审计定理(下界定理,可选);
色类偶矩接线(超多项式尾,给出更锐包络陈述;闭合不需要)。

## 4. 硬性纪律(违反须返工;与前几轮相同)

- 默认禁用 subagent(仅当用户当轮明确授权时例外);全部形式化亲自完成。
- 偏差自检:(a) 等式/不等式方向;(b) 前提真实消费;(c) 新前提全量词域可满足
  (最终前提 = 模型窗口 + b-带,带 `[ft, 1−(ft)²)` 非空,如实陈述);
  (d) **指数簿记逐项对表 §2**,任何偏离先手推再落 Lean。
- 编译证据:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`;
  公理 ⊆ 三公理 + 检查点四件套(裸名 sha256;时间戳用 date 实际输出);
  聚合写 `verification/build.log` 并追加 `verification/AxiomAudit.lean`
  (追加后整文件重编译至 exit=0);挂 import 后全量 `lake build Hurst`。
- land-then-follow-through:新鲜编译 → 检查点 → git commit → 增量 build →
  回写 VALIDATION_PROGRESS 与 TRANSITION。
- 小步优先;同一声明卡 >2 次同一错误,贴 trace_state 原文求助。
- 不碰 `ZCODE_VALIDATION_MONITOR.md`;文档编辑用 python 字符串手术。

## 5. 雷区(累积版在 VALIDATION_PROGRESS 置顶块;本轮相关摘录)

- **⚠️ 头号陷阱**:随机侧不得用 `truncExpectation_le_fluctuation`(sd 界,
  漂移 O(1));必须 TT:95 尾部型(V + ε)。已登记两轮勘误,勿第三次踩。
- rpow 指数算术:`Real.rpow_add/rpow_sub` 显式传正性前提;`S^{2ψ}` 与
  `(S^ψ)²` 的互化先具名引理(先例 NormalizedLogVariance:58 hscale);
  `div_le_iff₀` 族是 unicode ₀。
- Chebyshev 在 ℝ≥0∞ vs ℝ 之间:TT:58 是 ℝ≥0∞ 版,ℝ 版可用
  `ChebyshevMarkov`/方差版或自拼(测度换算先例见 TT 文件)。
- nlinarith 遇 cast 拆不开:先 `exact_mod_cast` 具名 have;单乘积原子先 rewrite。
- 大上下文复合展开超时:小上下文装配引理(ILSO 的 secondOrder_assembly 先例)。
- `Tendsto.congr'` 方向(takeover7 勘误):`hl : 已收敛 =ᶠ 目标`。

## 6. 汇报要求(诚实条款)

landed / not-landed 分列;任务 2 的两项指数与常数(Cst/Clog/W/U/C/gLSM)显式;
任务 3 的最终前提清单逐条列出并与"模型窗口 + b-带"核对;**端点闭环声明须待
协调者独立复审后生效**;编译日志路径 + 真实 exit code + 公理审计输出原文;
旧 hBias 端点的 legacy-空真标注如实写入文档,不得删除历史定理。
