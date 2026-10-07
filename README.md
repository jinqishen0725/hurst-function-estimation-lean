# Hurst function estimation — Lean audit

主要交付：[summary.md](summary.md)（逐项审计索引）与
[paper_revision/revised_theorems.tex](paper_revision/revised_theorems.tex)
（**修订后的长记忆主定理**，按正文 19-AOS1825 的 Theorem 3.3(iii)+3.4 长记忆
分支陈述，全部条件与结论机器验证）。

**状态（2026-10-07）：长记忆主线已闭环验收**——`Hurst/HonestRateClosure.lean`
的 `actualQ1_knownScaleH_fullChain_honestRate`：在模型窗口 + b-带 + r 下
`2 S^ψ log n (Ĥ_n − f t) ⇒ −Q`，Q 为构造的 signed 加权 Riesz 二阶混沌律；
聚合 build 9223 jobs 绿、2603 条定理公理 ⊆ 三标准公理、零 sorry，机器验收
`python3 verification/final_acceptance.py` 七项全过（commit 16715db / e76475a）。
未覆盖范围（短记忆/临界分支、minimax 程序的其余部分、未知尺度扩展、高维）
仍按 [backlog.md](backlog.md) 与 summary 逐项登记;代码地图见
[Hurst/README.md](Hurst/README.md)。

本轮修复定理与主要结论影响见 [repair_progress.md](repair_progress.md)。

现有20份数学证明文档见 [direct_proofs/README.md](direct_proofs/README.md)。当前重点已切换到这些证明的Lean补全；剩余数学扩展记录于 [backlog.md](backlog.md)，执行顺序见 [lean_roadmap.md](lean_roadmap.md)。

已补真实有限维Gaussian模型、Gaussian对数平方矩、加权对数统计量的期望/方差/MSE分解，以及多元Gaussian KL。[第三批](lean_batch3.md)进一步补完宽谱Frobenius界、Fano和Gaussian候选族到整个参数类的minimax下界传递。[lean_reuse.md](lean_reuse.md)记录外部库的采用状态。[第四批](lean_batch4.md)已完成实际一维谱特征、归一化和精确网格协方差。[第五阶段](lean_batch5.md)继续补完统一参数L²差界、V算子界及实际中点白化/KL等式。[第七阶段](lean_batch7.md)已补完整实际KL率和Proposition 8.1；[第八阶段](lean_batch8.md)已补完整Hölder packing、实际实验Fano和Theorem 3.1的原minimax liminf，包括p=1；[第九阶段](lean_batch9.md)完成固定值域子类下界及实际两端权重稳定性，[第十阶段](lean_batch10.md)完成原Hölder类的统一导数和实际全域偏差；[第十一阶段](lean_batch11.md)补出q=1真实全网格均值误差和谱函数高阶正则性；[第十二阶段](lean_batch12.md)补出Gaussian偶函数协方差及实际加权方差界；[第十三阶段](lean_batch13.md)补出实际q=1全网格行和与原类全域MSE；[第十四阶段](lean_batch14.md)已完成q=1已知尺度、1≤s≤2的最优带宽全域风险上界；[第十五阶段](lean_batch15.md)完成q=2原类p≥2、固定b<1的实际相关行和及对数均值方差；[第十六阶段](lean_batch16.md)完成q=2,p=2的已知尺度1≤s≤2全域最优风险；[第十七阶段](lean_batch17.md)推广到全部q=2,p≥2；s>2、未知尺度及极限仍待形式化；主线状态见[分项记录](mainline_status.md)。

## 重现

需要 `elan`。工程固定 Lean/mathlib v4.31.0，mathlib提交与依赖记录在 `lake-manifest.json`。

```sh
cd /Users/jinqishen/repo/lean_verification/hurst_function_estimation
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build > verification/build.log 2>&1
python3 scripts/check_coverage.py
lake env lean verification/AxiomAudit.lean > verification/axioms.log
python3 scripts/verify_axioms.py
python3 verification/final_acceptance.py   # 闭环后七项机器验收(含端点签名门禁)
```

全新克隆且没有 `.lake` 时先运行 `lake update` 获取固定依赖。首次安装依赖需要网络和数GB空间。工具链使用[Lean](https://github.com/leanprover/lean4)及[mathlib](https://github.com/leanprover-community/mathlib4)官方发布。

## 文件

- `Hurst/*.lean`：已验证的确定性/分析/概率恒等式及主链端点;分层地图与
  阅读顺序见 [Hurst/README.md](Hurst/README.md)。
- `paper_revision/revised_theorems.tex`：修订后主定理的论文式陈述(含与原稿
  及修复计划的逐条偏差表)。
- `paper_revision/theorem_inventory.md`：**原文 27 项定理/引理的逐项验证状态
  盘点**(已验证/已修复/仅书面/无结论四层 + 已验证的问题引理清单)。
- `verification/final_acceptance.py`：闭环后的七项机器验收脚本。
- `results/*.md`：正文13项、补充14项，每项单独记录，不将局部证明视为原定理证明。
- `results/catalog.json`：机器可读依赖与证据映射。
- `source/*.txt`：从用户提供的PDF提取的文本；数学歧义按原PDF页面核对。
- `verification/build.log`、`axioms.log`、`coverage.json`：实际编译、公理和覆盖记录。
- `scripts/build_catalog.py`：重建逐项说明与编号清单。
- `scripts/numerical_checks.py`：需要numpy的独立确定性数值诊断，不是Lean证明，也不是原论文模拟重现。

在本次桌面环境中，可用下面的Python运行数值诊断：

```sh
/Users/jinqishen/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 scripts/numerical_checks.py
```

- [第六阶段：实际冻结矩阵与完整谱下界](lean_batch6.md)

[第十八阶段](lean_batch18.md)已完成已知尺度、1≤s≤2的同类minimax平方Ls上下界（含显式可测估计核）。未知尺度、高阶矩与极限仍在主线。

[第十九阶段](lean_batch19.md)完成q=2未知尺度pilot实际全域MSE与精确尺度消去；最终尺度估计及回代仍在推进。

[第二十阶段](lean_batch20.md)完成q=2实际未知对数尺度MSE；全域粗平均及固定类区间截断的实现选择已注明。最终H回代风险继续推进。

[第二十一阶段](lean_batch21.md)补齐q=2实际未知尺度H回代和1≤s≤2平方Ls minimax；一个可测决策核统一处理所有σ≠0。主线仍缺q=1未知尺度、高阶矩及极限分布。

[第二十二阶段](lean_batch22.md)完成q=1短记忆、p≥1的实际未知尺度pilot、尺度平均和H回代，给出1≤s≤2全域平方Ls minimax匹配。下一主线为高阶矩及所列极限分布。

[第二十三阶段](lean_batch23.md)闭合Hermite完备性、实际Gaussian联合展开、精确二阶log系数及四阶余项相关界。剩余主线仍为多指标高阶矩、s>2风险、精细偏差与实际分布极限。

[第二十四阶段](lean_batch24.md)完成实际q=1短记忆及q=2全域、全固定Hurst类的一致Hermite截断L²误差，以及实际有界Lipschitz测试函数误差。有限多项式CLT、实际方差极限、高阶矩、精细偏差等仍缺。

[第二十五阶段](lean_batch25.md)从mathlib Taylor/矩阵连续性及已验证项目均值方差证明实际等价核和期望偏差首项；适用整数p、额外C^p、固定内部位置与精确最优带宽，q=2真H严格处于截断区间内部。截断反演余项仅需二阶矩。已知非零尺度已接通；CLT、高阶矩及未知尺度精细偏差仍缺。

[第二十六阶段](lean_batch26.md)补齐实际已知尺度估计器的随机线性化和变化样本空间的L¹弱极限传递。复用本地mathlib有界Lipschitz判据；其现有独立同分布CLT不能直接用于本文相关阵列，实际CLT仍待证。

[第二十七阶段](lean_batch27.md)按新顺序补出文件21并建立显式前提的Lean链；已消除q=1未知尺度期望首项的统计输入，q=2及分布传递仍见[条件登记](verification/conditional_results.json)。外部文献引理和内部待形式化引理分别列在[依赖表](verification/dependency_plan.md)。

第二十八阶段当前状态：所列外部及内部支撑前提下的一维下游 Lean 主线已接通，见[汇总](conditional_mainline_summary.md)。仅假设外部文献原引理的更强版本仍未完成，尤其 EXT-MOM→实际 QRawMomentBound 的桥接；最新状态以[条件登记](verification/conditional_results.json)为准。
