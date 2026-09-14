# 一维主线“收工”独立复核（2026-09-14）

结论：**不能按原验收口径认定主线完成。** 最新源码的 Lean 构建和公理审计均通过，但最终 q1 长记忆定理的前提不可满足，因此该定理没有证明任何实际模型实例的收敛。它的数学结论未被这个发现否定；需要修复定理陈述和分析估计后重新证明。

## 核验范围与可重复证据

- 核验提交：`9ba36f6`，对照阶段标签 `checkpoint-2026-09-10-mainline-transition`（`c2d8585`）。
- `lake build Hurst` 在当前源码上通过：`Build completed successfully (9126 jobs)`。独立日志保存在 `/tmp/hurst-audit-build-2026-09-14.log`。
- `lake env lean verification/AxiomAudit.lean` 在当前源码上通过；独立检查找到 2243 个已登记声明、0 个缺失、0 个 `sorryAx`、0 个自定义公理、0 个 Lean 错误。独立日志在 `/tmp/hurst-audit-axioms-2026-09-14.log`。
- `lake env lean verification/CapstonePremiseAudit.lean` 通过。该文件没有修改原定理，直接在 Lean 中证明下面两种前提矛盾。
- `verification/coverage.json` 仍写明完整原编号结果为 **2/27**；`verification/internal_input_inventory.json` 的 `mainline_complete: true` 不能代替检查定理前提是否可满足。`scripts/check_internal_inputs.py` 仅检查登记状态之间的布尔一致性。

## 阻断项 1：所有样本行非空的前提不可能成立

`Hurst/ActualSecondChaosComplete.lean` 的 `actualQ1LongStatistic_tendsto_secondChaos_complete` 把

```lean
hcard : ∀ n : ℕ,
  0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card
```

作为前提。`localWeightActiveSet n q δ t` 是 `Finset (Fin (n - q))` 的子集。取 `n = 0`, `q = 1` 时，`Fin (0 - 1)` 为空，故集合的 `card = 0`。Lean 反证是 `capstone_all_rows_cardinality_impossible`。

这一问题也出现在上游的 `actualQ1EigenvaluePowerSums_complete`、`ActualQuadratureFinal.lean` 的相关定理。渐近证明通常只需要 `∀ᶠ n in atTop, 0 < card n`；上游每一处使用都需逐项改为最终非空或用对小 `n` 安全的定义。

## 阻断项 2：两条多项式带宽限制相互矛盾

同一最终定理要求 `f(t) ≤ b < 1` 以及

```text
γ < 4 f(t) - 3                                      (hγcut)
4 b + 1 - 4 f(t) < γ (5 - 4 f(t))                 (hγdec)
```

由于 `b ≥ f(t)`，第二式左侧至少为 `1`。第一式和 `5 - 4 f(t) > 0` 则推出

```text
γ (5 - 4 f(t))
  < (4 f(t) - 3)(5 - 4 f(t))
  = 1 - (4 f(t) - 4)^2
  ≤ 1.
```

两者矛盾。Lean 反证是 `capstone_bandwidth_window_impossible`；`capstone_model_bandwidth_impossible` 直接使用原定理的 `MapsTo` 模型范围。**仅修正 `hcard` 不能解除这个阻断。** 需要重新估计冻结矩阵扰动或换一条证明路线，给出可同时满足的带宽区间，并展示至少一个合法参数实例。

## 其他仍需澄清的边界

- 最终定理还保留 `hRiesz : ∀ k ≥ 2, HasSum (λ_j^k) (Riesz cycle integral)` 和 `hQ : IsSecondChaosSeriesLaw P' Q λ`。这是极限谱与律的识别数据，不是普通的 Hölder/带宽模型条件。仓库中能找到以这些性质为前提的转移定理，但未找到从本文 Riesz 算子构造该 `λ` 与 `Q` 的存在性定理。若把它们作为外部结果，需给出精确文献定理和完整适用证明；否则仍是内部任务。
- `hwnn` 假设实际局部多项式权重最终非负。`LocalLinearWeightsNonneg.lean` 明确说明一般局部线性权重可为负，并只在一个额外平衡判据下证明非负。最终定理因此只覆盖特例，且在当前不相容带宽条件下该特例也不能完成长记忆结论。
- 短记忆 q1/q2 的 B&S 应用模块是真实新增工作，不能因长记忆最终定理空真而全部否定。但其单个有限 Hermite CLT 定理仍把截断方差极限 `hvar` 作为输入；要按“仅精确外部文献结果可假设”的口径验收，应检查每一个最终消费处是否用已证明的实际方差极限将它消去。`JoinedPilotActualMarginal.lean` 对最优带宽边际链做了此拼接，不能由此自动推出整篇论文的联合向量定理。
- `summary.md` 顶部“终局状态/主线完成”与其后旧状态及 `coverage.json` 的 `2/27` 并不一致。恢复可满足的最终定理之前，应把 `INT-LONG` 和 `mainline_complete` 改回待完成，并重写摘要中的完成范围。

## 对工作量的阶段性估算

Git 的 75 个后续提交统一显示同一个本机作者，因此不能把提交作者当作代理身份。以下只比较 **2026-09-10 检查点之前的既有阶段** 与 **检查点之后的收工阶段**，并非精确人时或个人归属：

| 口径 | 检查点之前 | 检查点之后新增 | 相对比例 |
|---|---:|---:|---:|
| `Hurst/*.lean` 文件 | 504 | 63 | 约 89:11（文件数偏向早期，因为后期文件较大） |
| Lean 源码行数 | 约 52,958 | 净增约 21,761 | 约 71:29 |
| 同一正则口径统计的 theorem/lemma 声明（含 private/protected） | 1,859 | 净增 547 | 约 77:23 |
| 书面证明、逐编号核查、来源、模拟与审计框架 | 主要在检查点之前 | 后期以长记忆拼接和新证明为主 | 不宜折算成单一数字 |

更正：此前用覆盖登记的 1,152 与 2,240 推算“新增 1,088、比例 51:49”不可靠，因为检查点的登记已经落后于实际源码，后续还扩充了覆盖采集。上表改为对两个阶段使用相同源码匹配规则。该规则只作同口径数量比较，不等于全部 Lean 声明的语法分析。此前整体投入 **6:4** 也是主观估计，不能由这些数字验证；仅凭 Git 无法可靠估计人时。早期建立了更广的数学与代码基础，后期对谱匹配、Riesz 截断和实际 CLT 做了大量实质性工作；工作量与最终定理是否完成须分别判断。

## 修复后重新验收

1. 把全部相关 `∀ n, 0 < card n` 改为真正需要的最终非空条件，并直接证明它来自 `nδ → ∞`。
2. 重新推导可行的带宽不等式；在 Lean 和普通实数例子中展示前提可同时满足。
3. 完成极限谱 `λ` 与二阶混沌律 `Q` 的构造/识别，或严格匹配可保留的外部文献定理。
4. 用修正后的实际前提推出非空的 q1 长记忆结果，并对最终估计器而非只对二次统计量补齐传递。
5. 对 `Hurst.lean`、覆盖、公理、内部输入和逐编号状态运行同一源码快照的全套检查。

本次审计只新增了独立复核文件，没有修改对方的 Lean 主线或历史提交。

后续书面交接：见[文件22](../direct_proofs/22_long_memory_repair_lean_handoff.md)。它进一步证明可直接去掉 `hγdec` 与不必要的 `hγcut`，以无维数损失的迹估计重组主线；该新组合尚待 Lean 验证。汇总页已补上审计更正，未修改 Lean 主线。
