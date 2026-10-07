# Session-4 接管任务书(takeover9):统计闭环收尾——E5BiasExpansion 集成 + 二阶增量精化 + 超多项式集中 → hBias 消解

## 0. 环境与对象

- 工作目录:`/Users/jinqishen/repo/lean_verification/hurst_function_estimation`
  (Lean 4.31.0 / mathlib v4.31.0,arm64;git 仓库,HEAD = `ea83165`,提交链见 §1)。
- 里程碑状态:takeover8 双线程已完成并经独立审计(hane 谱式消解 + hband 中心带
  消解落地;审计发现 CBD 漏挂聚合树已修复)。**当前最强端点 =
  `Hurst/CenterBandDischarge.lean:717`
  `actualQ1_knownScaleH_fullChain_generalSigned_feasible_centerBand_zeroDof`**:
  前提 = 模型窗口 + b-带 `(1−f t)² < 1−b` + cσ + (C, hBias)。
  **端点 conditional 仅余 hBias 一个数据前提**;既得成果不得回退。
- 工作区注意:`Hurst/E5BiasExpansion.lean`(1030 行)+ 检查点
  `verification/checkpoints/2026-10-06-0829-E5BiasExpansion/` 为**未跟踪**状态
  (takeover8-parallel 第二 agent 的产物,来源已经审计者确证,见任务 1)。
  其余应干净(仅协调员的 `ZCODE_VALIDATION_MONITOR.md`,勿碰)。
- 本轮里程碑:任务 1(集成)→ 任务 2(二阶增量精化,本轮核心)→
  任务 3(集中不等式与截断转移)→ 任务 4(hBias 消解与最终端点)→
  任务 5(余量)。聚合验收基线 = `lake build Hurst` 9216 jobs 绿、
  AxiomAudit exit=0 且全 ⊆ {propext, Classical.choice, Quot.sound}、零 sorry。

## 1. 已落地快照(takeover8 + 审计修复;全部 exit=0、零 sorry、公理 ⊆ 三公理)

- **hane 已消解**(cb61f12,`Hurst/FeatureRowNondegenerate.lean`,12 定理):
  核心 `normalizedVaryingIncrement_ne_zero`(:227,∀ h k ∈ Ioo 0 1 ∀ s ℓ>0;
  整倍论证 + 两点范数平衡,经审计者逐行复核);
  回灌定理 `actualQ1_hane_discharged`(:663)/`actualQ1_hane_all`(:682);
  FeasibleRates 两端点 hane 前提已删(内部派生)。
- **hband 已消解**(997a3c5,`Hurst/CenterBandDischarge.lean`,5 定理):
  期望分解(:68)、增量对数界(:128)、**带比极限**(:209,任意固定 cσ,
  ∑w=1 来自先例 `localPolynomialWeights_uniform_stability` LocalWeights.lean:56
  的 k=0 矩)、`centerBand_hband_discharged`(:641,显式 d=(1−ft)/2)、
  端点(:675)与 zeroDof(:717,β 内部实例化,commit e1445ac)。
- **审计修复**(ea83165):CBD 漏挂 Hurst.lean 已补(:678),聚合 9216 绿,
  AxiomAudit 恢复 exit=0。
- **E5BiasExpansion(未集成)**:并行 agent 四块全落地——
  `truncExpectation_le_fluctuation`(:124,抽象)、
  `varyingIncrement_norm_sq_error`(:174,**诚实率 n^{−(1−b)}**)、
  `holderWeightContraction`(:329,+实例链 :460)、
  `p5KnownScaleHtilde_expectation_eq`(:618,精确恒等式)、
  `p5KnownScaleHtilde_drift_bound`(:745)、
  **`knownScaleEstimator_bias_envelope_grid`**(:885,条件定理:前提含
  hane/hw1/hγ : γ ≤ 1−b/hcσ : cσ = gaussianLogSquareMean/hbandc/hfluct,
  结论 |E Ĥ − f t| ≤ (F+Cst+Clog·W/2)·n^{−γ});
  接口恒等式 `chainLogStatistic_eq_rpow_smul`/`chainCalibratedStatistic_eq`。
- 文档:VALIDATION_PROGRESS 置顶块(2026-10-06)、TRANSITION §0、
  hBias 四项里程碑条目(ebe6c2b)。

## 2. 必读文档与顺序

1. `VALIDATION_PROGRESS.md` 置顶块(2026-10-06):takeover8 落地表 + hBias
   四项里程碑 + 14 条雷区批。
2. 消费面(逐行核对,行号已验证):
   - `Hurst/E5BiasExpansion.lean` 全文(集成对象;:885 条件定理的前提清单);
   - 二阶精化的机械:`Hurst/Harmonizable.lean` — inner :183、
     **inner_formula :248**(精确核积分)、norm_sq :288、inner_same :314、
     increment_norm_sq :323;`Hurst/VaryingIncrement.lean:37`(一阶 uniform
     remainder,即 n^{−(1−b)} 的来源);
   - 集中不等式机械:`Hurst/WeightedEvenMomentBound.lean:19`
     `bardetSurgailis_weighted_evenMoment_bound`(∀k 阶偶矩,
     前提 hBS/hGaussian/hstandard + ε-相关行界 hrow——与近/远带结构对接);
   - 截断机械:`Hurst/P5LogHLayers.lean:69`(p5Trunc01_eq_self)、
     `Hurst/P5L1Joining.lean:108`(lipschitz);
   - 期望公式:`Hurst/GaussianLog.lean:153`(gaussianLogStatistic_expectation)、
     :82(gaussianLogSquareMean);
   - 旧波动率路线及其死因:`Hurst/E5RateLink.lean:300`
     (e5_fluctuation_rate_of_window;其 hmesh/hwin 联立在 γ = f t 处判别式 < 0
     恒不可解——并行 agent 已登记,勿再走)。
3. `TRANSITION_session4_2026-09-21.md` §0(2026-10-06 快照)与 §3/§4。

## 3. 结构性事实(先数学后 Lean;本轮路线的依据,已手推,落地时逐条验证)

**一阶路线在可行带宽下不可行(这就是必须做二阶的原因)**:
(a) `hF : MapsTo f (Ioo 0 1) (Icc a b)` ⟹ `f t ≤ b`,故 `b ≥ f t > 3/4`;
(b) 一阶增量对数率 n^{−(1−b)} 拟入 hBias 的 n^{−γ} 需 `γ ≤ 1−b`;
(c) 在 γ = f t 处即 `f t ≤ 1−b ≤ 1−f t` ⟹ `f t ≤ 1/2`,与 hlong(3/4 < f t)
    矛盾;一般地 hE5(⟺ γ > ψ/(1+ψ),ψ = 2−2f t)∧ γ ≤ 1−b ∧ b ≥ f t
    对 f t > 1/2 无解。**可选子任务:把 (a)(b)(c) 写成 Lean 矛盾审计定理
    (入 verification/,风格同 Session3PremiseAudit)。**
**二阶路线充分且门槛极低**:目标率只需 **n^{−(1+ε)}(任意 ε > 0)**——
因为 γ = f t < 1 < 1+ε,故 `n^{−(1+ε)} = O(n^{−γ})` 自动成立;
瞄准值 n^{−(2−b)}(2−b > 1 恒真)。二阶展开:
`‖varying‖² = 1 + 2⟨frozen, v−f⟩ + ‖v−f‖²`,交叉项
`⟨frozen, v−f⟩ = ℓ^{−2h}⟨F_h(s+ℓ)−F_h(s), F_k(s+ℓ)−F_h(s+ℓ)⟩`
用 Harmonizable:248 的精确核积分展开(双增量乘积的显式积分,
h−k 失配因子 |h−k|·log|ξ|-型被 ℓ^{-尺度} 吸收),避开 :37 的粗糙三角。
**随机侧同理需换轨**:截断修正 `|E trunc(H̃) − E H̃| ≤ E|H̃−EH̃|·1_{H̃∉[0,1]}`
的 Chebyshev/波动率界都到不了 n^{−γ}(Var 侧只给 n^{−4(1−f t)²};
E5RateLink 窗口不可解)。换轨:用 WeightedEvenMomentBound:19 的 ∀k 阶偶矩
+ Markov 取 `k := ⌊log n⌋` ⟹ 尾概率超多项式小(n^{−c·log log n} 级)
⟹ 截断修正 ≪ n^{−γ}。注意前提对接:hBS/hGaussian/hstandard 对
standardizedFeatureObservation 族应已有先例(自行 grep
standardizedFeatureObservation_law 等),ε-相关行界用近/远带(同阻断 3 的
far envelope 形状)。

## 4. 任务序列(按序;小步优先,每步独立落地)

任务 1 = **集成 E5BiasExpansion**(来源已审计确证):
`Hurst.lean` 追加 `import Hurst.E5BiasExpansion`(放 CBD 之后);AxiomAudit
追加其 17 条(至少 :124/:174/:205/:329/:460/:618/:745/:885 与两条接口恒等式);
顺手把 :885 的 hane 前提用 `actualQ1_hane_all`(FRN:682)消解、hw1 用
LocalWeights:56 的 k=0 矩消解(若便宜;否则保留前提并登记);
commit 文件 + 检查点 + 文档表更新;全量 build + AxiomAudit exit=0。
任务 2 = **二阶增量对数精化**(本轮核心,建议新文件
`Hurst/IncrementLogSecondOrder.lean`):
目标定理:`∃ C, ∀ n H j, |log‖gridStrideFirstActual n 1 H j‖²| ≤ C·n^{−(1+ε)}`
(ε 显式给出,瞄准 1−b>0 使 1+ε = 2−b;证明走 Harmonizable:248 精确展开;
先小上下文引理后组装——复合 defeq 展开超时的老雷区)。
诚实条款:若二阶率只能证到 (1+ε) 中更小的 ε,如实登记并检查是否仍 > 0
(任意 ε > 0 即足以支撑任务 4);若被证伪,停手登记。
任务 3 = **集中不等式与截断转移**(建议 `Hurst/TruncationTransfer.lean`):
(a) 偶矩→尾概率:对 H̃ = p5KnownScaleHtilde(cσ := gaussianLogSquareMean),
用 WeightedEvenMomentBound:19 + Markov(k := ⌊log n⌋)得
`P(H̃ ∉ Icc 0 1) ≤ n^{−c}` 任意固定 c(或超多项式形状,如实陈述);
(b) 截断转移:`|E p5Trunc01(H̃) − E H̃| ≤ C_T·n^{−γ}`(组合 truncExpectation_
le_fluctuation(E5B:124)的形状 + (a) 的尾界 + Var 界);
hBS/hGaussian/hstandard/ε-行界与模型的对接引理若缺,先补小引理。
任务 4 = **hBias 消解与最终端点**:
以任务 2 的率替换 :885 的 hlog、任务 3 的界替换 hfluct、cσ := gaussianLogSquareMean
钉死、hbandc 用 CBD:641 的带结论派生,组装
`hBias_discharged : ∀ᶠ n, |E Ĥ_n − f t| ≤ C·n^{−γ}`(C 显式),
再回灌 zeroDof 端点 ⟹ **最终端点**(暂名 `…_feasible_centerBand_hBias`):
前提只剩 模型窗口 + b-带(C 内部显式或外部给出,如实陈述)。
聚合验收四件套 + 文档回写(消解表 hBias 行 → RESOLVED,或如实标
partial)。**在 hBias 真正消解并复审前,不得宣称"统计闭环/无条件化"。**
任务 5(余量)= expectation-centered / unknown-scale 变体镜像
(旧 FullChainEndpoint 三变体格式);backlog/TRANSITION 收尾;
§3 的可选矛盾审计定理。

## 5. 硬性纪律(违反须返工;与前几轮相同)

- 默认禁用 subagent(仅当用户当轮明确授权时例外);全部形式化亲自完成。
- 落地前偏差自检:(a) 等式/不等式方向;(b) 前提真实消费;(c) 新前提
  全量词域可满足;(d) "更强定理回灌端点"逐点替换并声明,不做全局重写。
- 编译证据:`lake env lean <file> > /tmp/<log> 2>&1; echo "exit=$?" >> /tmp/<log>`;
  公理 ⊆ 三公理 + 检查点四件套(裸名 sha256;/tmp 审计前先 lake build 刷新;
  时间戳用 date 实际输出);聚合写 `verification/build.log` 并追加
  `verification/AxiomAudit.lean`(追加后必须整体重编译 AxiomAudit 至 exit=0
  ——takeover8 的 CBD 漏挂教训)。
- land-then-follow-through:新鲜编译 → 检查点 → git commit → 增量
  `lake build Hurst` → 回写 VALIDATION_PROGRESS 与 TRANSITION。
- 小步优先;同一声明卡 >2 次同一错误,贴 trace_state 原文求助。
- 不碰 `ZCODE_VALIDATION_MONITOR.md`;文档编辑用 python 字符串手术。

## 6. 雷区(累积版在 VALIDATION_PROGRESS 置顶块;takeover8 批摘录 + 本轮相关)

- 复合算子/大上下文 defeq 展开超时:提取小上下文独立引理(6a 节老雷区,
  任务 2 的精确核积分展开同样适用)。
- `Tendsto.congr'` 方向(takeover7 勘误):`hl : 已收敛 =ᶠ 目标`。
- `by linarith` 遇隐式元变量失败:显式类型化 have;单乘积原子先 rewrite;
  field_simp+linarith 原子归一冲突 → linear_combination 或单项式形式。
- rpow/log 签名族、Complex cast push-in、lt_of_le_of_ne 方向、
  div_eq_iff 族、构建环检测(feedback 端点放上游文件尾部)——takeover8
  14 条批见置顶块。
- log(1+x) 型界先手证子引理;期望/截断交换方向自检;
  积分>0 先正测集再正性引理。
- Markov 取 k := ⌊log n⌋ 时注意偶矩常数 D 对 k 的依赖形状
  (WeightedEvenMomentBound:19 的 D 是存在量词,对 k 非一致——需读取其
  证明拿到显式 k-依赖或按 k 归纳,如实处理,不得默默当作一致常数)。

## 7. 汇报要求(诚实条款)

landed / not-landed 分列;任务 2 的 ε 与证明路线、任务 3 的尾概率形状、
任务 4 的 C 显式值必须如实给出;一阶不可行性(§3)若写成 Lean 审计定理,
附其公理审计;hBias 消解前不得宣称统计闭环;编译日志路径 + 真实 exit code +
公理审计输出原文;E5BiasExpansion 集成的每一步(import/审计行/前提消解)
逐项列出。
