# Hurst/*.lean — 模块地图与阅读顺序

本文件是代码库的可维护性入口:分层依赖图、推荐阅读顺序、每层关键定理、
端点索引与验证工作流。**主链已于 2026-10-07 闭环验收**(commit `16715db`,
机器验收 `verification/final_acceptance.py` 七项全过);修订后的定理陈述见
`paper_revision/revised_theorems.tex`。

## 分层结构(自底向上)

```
L0 模型与基础原语
   HolderRegularity, Harmonizable, VaryingIncrement, FirstStride*,
   GridCorrelation*, LocalWeights, ActiveSet*, GaussianFinite, GaussianLog*
      ↓
L1 特征/相关/核的定量层
   ActualFirstLong*(HS 逼近), KernelEnergyRateDischarge, GridErrorRate,
   WeightedEvenMomentBound, FirstScaleLongRates, ActualCorrelation*Tail
      ↓
L2 谱与二阶混沌(阻断 1/4 消解线)
   CountableEigenfamily, EquivalentKernelSpectrum, BopCompactness,
   CompressionIdentity, CompressionGeneralK(M1:压缩恒等式+谱识别),
   IntervalL2Basis → WeightedRieszSpectrumClosed(闭谱,三前提),
   PeelingInduction, LevelCakeTransfer, SpectralPermutation, P3SignedMatching,
   GeneralSignedPowerMatching, SignedInterleavedLaw, SignedPowerLimit
      ↓
L3 实际模型能量与余项(阻断 3 消解线)
   NormalizedHermiteEnergy → NormalizedActualEnergy → NormalizedActualRemainder,
   NormalizedLogVariance, NormalizedLogProjection
      ↓
L4 特征行非退化与谱式消解(阻断 2/hane 消解线)
   FeatureRowNondegenerate(normalizedVaryingIncrement_ne_zero)
      ↓
L5 二次端点与其构造极限律
   ActualQ1SignedClosed(actualQ1LongStatistic_tendsto_secondChaos_generalSigned)
      ↓
L6 P5 层(log → seam → transport)
   P5L1Joining, P5LogHLayers(Layer 1 与 Layer 1′ double-sum 形),
   P5SeamClosed(seam 核心 + 通用核 seam_of_logLimit), P5TruthCenter,
   P5JoinInstantiation, E5ChainInstantiation, E5RateLink
      ↓
L7 诚实率与最终组装
   FeasibleRates(标量率), IncrementLogSecondOrder(二阶增量率),
   TruncationTransfer(尾部型截断转移), HBiasSecondOrder(包络+窗口审计),
   CenterBandDischarge(hband 消解 + zeroDof 端点),
   UnitVarianceRate, HonestRateDrift, HonestRateClosure(★ 主端点)
      ↓
L8 历史端点(legacy,勿删)
   FullChainEndpoint(hBias 前提在 γ=ft 对变剖面空真,已标注),
   CapstoneV2/V3, ActualQuadratureFinal, FrozenQuadClosed 等条件线
```

## 推荐阅读顺序(新接手者)

1. `paper_revision/revised_theorems.tex` — 定理是什么、条件是什么。
2. `Hurst/HonestRateClosure.lean`(327 行)— 主端点的组装骨架。
3. 逆着骨架读:`HonestRateDrift.lean`(漂移两项分解)→
   `TruncationTransfer.lean` + `UnitVarianceRate.lean`(随机侧)→
   `IncrementLogSecondOrder.lean` + `E5BiasExpansion.lean:752`(确定性侧)。
4. 谱侧:`WeightedRieszSpectrumClosed.lean` → `CompressionGeneralK.lean`(M1)→
   `SignedPowerLimit.lean` / `GeneralSignedPowerMatching.lean`。
5. 历史:`VALIDATION_PROGRESS.md` 置顶块(十轮接力的落地表与雷区累积)。

## 端点索引(按强度)

| 端点 | 文件 | 前提 | 状态 |
|---|---|---|---|
| `actualQ1_knownScaleH_fullChain_honestRate` | HonestRateClosure | 模型窗口+b-带+r | **★ 主线,已验收** |
| `…_feasible_centerBand_zeroDof` | CenterBandDischarge:717 | + cσ + (C,hBias) | legacy(hBias 空真) |
| `…_feasible_centerBand` | CenterBandDischarge:675 | + β | legacy |
| `…_generalSigned_scalarRates / _feasible` | FeasibleRates:390/:453 | + γ 自由 | 一般 γ 条件形 |
| `actualQ1_knownScaleH_fullChain*` | FullChainEndpoint | D3 旧前提 | legacy(审计对照用) |

## 关键不变量(维护时的红线)

- 公理永远 ⊆ {propext, Classical.choice, Quot.sound};零 sorry。
- 不得为接口方便重新引入已消解/已证伪的前提:hm(∀n 非空)、hE2(未归一化
  能量)、hNegMass、hconst、hBias@n^{−ft}(窗口不可行,HBiasSecondOrder:230/:240)。
- 随机侧截断修正必须走尾部型 `truncationCorrection_le`(V+ε);crude sd 界
  (`truncExpectation_le_fluctuation`)喂进漂移得 O(1)——两次勘误钉死的陷阱。
- 挂新模块进 `Hurst.lean` 后必须整文件重编译 `verification/AxiomAudit.lean`
  至 exit=0(takeover8 漏挂教训);跑 `python3 verification/final_acceptance.py`。

## 验证工作流

```sh
lake build Hurst                                  # 聚合(约 2 分钟冷构建)
lake env lean Hurst/<File>.lean                   # 单文件重阐述
lake env lean verification/AxiomAudit.lean        # 全量公理审计(须 exit=0)
python3 verification/final_acceptance.py          # 七项机器验收(A–G)
```

检查点纪律:每笔实质落地配 `verification/checkpoints/<date-time>-<track>/`
(源快照 + compile.log + axioms.log + sha256.txt,目录内裸名)。
雷区累积表(v4.31/v4.32 的 Lean 用法坑)在 `VALIDATION_PROGRESS.md` 置顶块。
