# 里程碑 1 数学契约:消除 hconst 的真实等价核谱对象与循环积分桥

日期:2026-09-18。依据:审查阻断 1(`verification/Session3PremiseAudit.lean` 已 Lean 证明
hconst 不可满足)、书面方案 22:W6 与 23:A4–A6。本契约冻结定理签名;任何偏差必须
声明式回写本文件与 `VALIDATION_PROGRESS.md`。

## ⚠️ 契约更正记录(2026-09-18 协调检查,已传达给全部执行 agent)

1. **§2 非负性遗漏 `hc : 0 ≤ c`**:c < 0 时非负结论为假(eigenvalues/二次型按 c 缩放)。
   已把 `hc` 纳入两个非负性签名;对称/HS/紧性不需要它。实际模型 c = h(2h−1) > 0(h > 1/2)。
2. **§3 `exists_positive_sqrt` 的合取 `∀ i, ‖S v_i‖ = 1 ∨ S v_i = 0` 为假**
   (反例 T = 4·Id:‖S v‖ = 2),已删除。正确结论集:S v_i = √κ_i•v_i(范数 √κ_i)、
   S² = T、自伴、S 非负(⟪x,Sx⟫ ≥ 0)。每个 ∀ 明确包住各自合取,防作用域滑落。
3. **§3 `mulOperator` 需本质有界**:仅可测的 ω 不能在全体 L2 上定义有界乘法算子。
   签名改为 `Measurable omega` + 本质界(`∀ᵐ x ∂vol, |omega x| ≤ MR`;或逐点界),
   并新增作用引理 `⇑(M_ω) f = ω • f`(a.e./Lp 余积意义)。
   **`exists_B_selfAdjoint_hs` 必须把 B 绑定为 `S ∘ M_ω ∘ S`**(S 为同一 T 的正平方根,
   S² = T),矩阵公式 ⟪v_i, B v_j⟫ = √(κ_iκ_j)⟪v_i, W v_j⟫ 作为命名合取——裸
   "存在自伴 HS 的 B"被零算子平凡满足,不接受。
4. **§4 `hBridge_clm` 需 HS 型条件**:紧性不推出谱平方可和(反例 κ_n = 1/√(n+1)),
   且非可和 tsum 有 Lean 默认值(不可当存在性)。已加:基一致 HS 型假设
   (T 的矩阵平方和可和且有界;下游由 M1-B 的 A7 交付,不是新最终模型假设),
   并把 `Summable (val ^ 2)` 作为**结论**同时证明;对角和以 HasSum + 已证可和性陈述。
5. **§5 降级为草案**:仍含 hconst'/省略号占位,非冻结签名。A/B/C 落地后先写可检查的
   最小接口(构造 B、真实谱枚举、k=2 与所有 k≥3、可满足实例),再派发。
   阶段性缺口记录在案但**不算 M1 验收通过**。
6. **Hilbert 基存在是内部待证事项**,不是已完成的环境数据(见 §1 表格更正:
   状态从"✅ 环境数据"改为"⏳ 内部待证(唯一残余,见 §5)")。

## 0. 根因与修复原则

现线路的算子是 `TOp (rieszKernel psi c omega)`,核为 `ω(x)·c·|x−y|^{−ψ}`(W 作用于行)。
`ω(x)K(x,y) ≠ ω(y)K(y,x)` 一般非自伴;原 hconst 用常数 ω 强行保证对称,而实际
`ω = equivalentKernel r` 非常数(积分为 1、非常数多项式调制核),矛盾已 Lean 证明。

修复:**谱对象换成 `B = K^{1/2} W K^{1/2}`**(22:W6 / 23:A4–A6),其中
`K = c·|x−y|^{−ψ}` **无权**(对称 ⇒ 自伴),`W = M_ω`(有界自伴乘法算子,不要求 ω≥0)。
B 构造性自伴;其谱 `(μ_j)` 平方可和,且 `∑' μ_j^k = tr(B^k) = tr((WK)^k) = J_k^ω`,
`J_k^ω` 恰是**已存在**的 `Hurst.weightedRieszCycleIntegral k psi c omega`
(左乘 ω(x) 本身就是核运算:`M_ω ∘ TOp_K = TOp_{(x,y)↦ω(x)K(x,y)}`,
后者即现有 `rieszKernel psi c omega` —— **循环积分一侧无需任何重定义**)。

一切在 `E := HS.L2`(vol = I=[−1,1] 上 Lebesgue 限制)上进行。

## 1. 模型前提及其在实际模型中的证明(逐一列出)

| Lean 前提 | 实际模型(ω = equivalentKernel r, 0 < ψ < 1/2)中如何证明 | 状态 |
|---|---|---|
| `homega : Measurable omega` | `equivalentKernel_continuous`(EquivalentKernel.lean,连续 ⇒ 可测) | ✅ 已落地 |
| `hbdd : ∀ x, \|omega x\| ≤ MR` | `equivalentKernel_bounded`(ActiveWeightProfile.lean:59) | ✅ 已落地 |
| `hpsi2 : 2 * psi < 1` | capstone 可行带宽(f t > 3/4;已有 hg 同款) | ✅ 数据前提 |
| `hpsi0 : 0 < psi` | f t < 1 ⇒ ψ = 2−2f t > 0 | ✅ 数据前提 |
| unweighted K 的 HS 性 | `fract_section_bound`(RieszSectionBounds,ω≡1 情形直接可用):uniform section L² 界 ⇒ ∫∫ K² < ∞ | ✅ 工具已落地 |
| W 有界自伴 | 新小引理:`ω` 可测 + 本质有界 ⇒ `M_ω : L2 →L[ℝ] L2`、`IsSymmetric`、`‖M_ω‖ ≤ MR`、作用 a.e. 引理(§3 修正 3) | 🆕 M1-B(机械) |
| K 非负(κ_i ≥ 0) | A5 Laplace/Γ 表示(**已落地** `RieszOperatorPositivity.laplace_rpow_neg` 供给 Γ–Laplace)+ **已落地** `HS.kernelPSD_exp_dist`(e^{-u\|x−y\|} PSD,u>0)的混合;需 `hc : 0 ≤ c` | 🆕 M1-A(核心难点) |
| K 紧 | HS 核算子紧性:沿用 `isCompactOperator_TOp_riesz`(RieszCompactEnumeration:95)的证明骨架(该证明不依赖 ω/常数性) | 🆕 M1-A(骨架复用) |
| Hilbert 基 `e` | **内部待证事项**(非已完成环境数据):需构造 `HilbertBasis ℕ ℝ L2`(可分性 + Gram–Schmidt,mathlib v4.31 无现成 API;或由 EigenFamilySplice 可数特征族转换)。整个 HS 层以其为环境参数,结论与 e 无关 | ⏳ 唯一记录在案残余 |

**没有**任何"普通假设"打包内部待证条件:每个新定理的前提要么是上表已证明的模型事实,
要么是冻结接口的输出。

## 2. 冻结接口(M1-A → M1-B/M1-D)

模块 `Hurst/UnweightedRieszOperator.lean`(namespace HS):

```lean
def unweightedRieszKernel (psi c : ℝ) : ℝ × ℝ → ℝ :=
  fun p => c * |p.1 - p.2| ^ (-psi)

theorem unweightedRieszKernel_symm (psi c x y : ℝ) :
    unweightedRieszKernel psi c (x, y) = unweightedRieszKernel psi c (y, x)

theorem hsKernel_unweightedRieszKernel {psi c : ℝ} (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1) :
    HSKernel (unweightedRieszKernel psi c)

theorem isSymmetric_TOp_unweightedRiesz {psi c : ℝ} (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1) :
    (↑(TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2)) : L2 →ₗ[ℝ] L2).IsSymmetric

theorem isCompactOperator_TOp_unweightedRiesz {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) :
    IsCompactOperator (TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel hpsi0 hpsi2))

/-- A5:无权 Riesz 算子非负(Laplace/Γ 表示 + exp-核 PSD 混合)。c 的符号必须追踪。 -/
theorem inner_TOp_unweightedRiesz_nonneg {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hc : 0 ≤ c)
    (f : L2) :
    0 ≤ inner ℝ (TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) f) f

/-- 完备非负特征族(K 的;κ ≥ 0 由非负性 + 特征方程)。c 符号追踪同上。 -/
theorem exists_nonneg_eigenfamily {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hc : 0 ≤ c) :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ), Orthonormal ℝ v
      ∧ (∀ i, TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i) = κ i • v i)
      ∧ ((span ℝ (Set.range v))ᗮ = ⊥)
      ∧ (∀ i, 0 ≤ κ i) ∧ Summable (fun i => κ i ^ 2)
```

要点:对称性从 `|x−y| = |y−x|` 平凡得出(**这就是消除 hconst 的地方**);A5 的非负性
走 `|x−y|^{−ψ} = Γ(ψ)^{-1}∫_0^∞ s^{ψ−1} e^{−s|x−y|} ds` + Tonelli/Fubini +
`kernelPSD_exp_dist`(已落地);Γ 表示查 `Real.Gamma*`(mathlib v4.31;若名字不符,
由 `Γ(ψ) = ∫_0^∞ e^{−u} u^{ψ−1} du` + 代换 `u = s·t` 自证,属机械)。

## 3. 冻结接口(M1-B → M1-D)

模块 `Hurst/PositiveSquareRoot.lean`(namespace HS):

```lean
/-- 有界(本质有界)且**可测**的乘法算子:两个前提都必须——仅可测不足以有界,
    有界非可测也不足以充当 L2 乘子。实际模型由 `equivalentKernel_continuous`/
    `equivalentKernel_bounded` 消解(连续 ⇒ 可测)。 -/
def mulOperator (omega : ℝ → ℝ) (hm : Measurable omega)
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) : L2 →L[ℝ] L2
theorem mulOperator_action {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    ⇑(mulOperator omega hm hess) f =ᵐ[vol] (fun x => omega x * ⇑f x)
theorem mulOperator_symm {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    (↑(mulOperator omega hm hess) : L2 →ₗ[ℝ] L2).IsSymmetric
theorem norm_mulOperator_le {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    ‖mulOperator omega hm hess‖ ≤ MR

/-- 正平方根(定义在完备非负特征族上,Parseval 收敛)。
    结论:S v_i = √κ_i•v_i(范数 √κ_i)、S² = T、自伴、S 非负。
    注意:不存在"‖S v_i‖ = 1 ∨ S v_i = 0"这类合取(假:反例 T = 4·Id)。 -/
theorem exists_positive_sqrt {T : L2 →L[ℝ] L2}
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i) :
    ∃ S : L2 →L[ℝ] L2, (↑S : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ (∀ i, S (v i) = Real.sqrt (κ i) • v i)
      ∧ (∀ x, S (S x) = T x)
      ∧ (∀ x, 0 ≤ inner ℝ x (S x))

/-- A7:B **绑定**为 B = S ∘ M_ω ∘ S(S 为同一 T 的正平方根,S² = T——裸"存在自伴
    HS 的 B"被零算子平凡满足,不接受)+ 矩阵公式 + 基一致双平方和界。 -/
theorem exists_B_selfAdjoint_hs {omega : ℝ → ℝ} {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR)
    {T : L2 →L[ℝ] L2} {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) :
    ∃ B : L2 →L[ℝ] L2,
      B = (exists_positive_sqrt …).choose ∘ mulOperator omega hess ∘ (…).choose
      ∧ (↑B : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ (∀ i j, inner ℝ (v i) (B (v j))
          = Real.sqrt (κ i * κ j) * inner ℝ (v i) ((mulOperator omega hess) (v j)))
      ∧ (A7 界:任意 HilbertBasis e 上 ∑' p, (⟪e p.1, B (e p.2)⟫)² ≤ MR ^ 2 * ∑' i, κ i ^ 2,
         且该二重级数 Summable)
```

(签名细化权在 M1-B 执行者,但:①B 以定义等式绑定到 `S∘M_ω∘S`;②A7 双平方和界
`≤ ‖ω‖∞²·∑κ²`、可和性;③`B (v i)` 的 `√(κ_iκ_j)`-矩阵结构必须作为命名定理可独立
消费——M1-D 依赖这三件。签名细化后**必须回写本文件**。)

## 4. 冻结接口(M1-C → M1-D)

模块 `Hurst/EndLevelTraceBridge.lean`(namespace HS):把 `EigenTraceBridge.hBridge`
从"核算子 `TOp K hK`"泛化到"抽象紧自伴 CLM/End"(H 的证明只用了算子结构):

```lean
theorem hBridge_clm {T : L2 →L[ℝ] L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hTcompact : IsCompactOperator T)
    -- 紧性不推出谱平方可和(反例 κ_n = 1/√(n+1)),必须显式加 HS 型条件;
    -- 该条件由 M1-B 的 A7 交付,不是新的最终模型假设:
    (hTHS : ∃ C : ℝ, 0 ≤ C ∧ ∀ e : HilbertBasis ℕ ℝ L2,
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (T (e p.2))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (T (e p.2)) ^ 2)) ≤ C)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T.toLin') val vec)      -- 与既有 IsDiagEnum 的 End/CLM 对齐
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T.toLin') μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ} = Module.finrank ℝ (Module.End.eigenspace (T.toLin') μ))
    (j : ℕ) (hj : 2 ≤ j) (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun m => val m ^ 2)                              -- 新增结论:不得依赖 junk tsum
      ∧ HasSum (fun i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) (∑' m : ℕ, val m ^ j)
      ∧ ((∑' i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) = ∑' m : ℕ, val m ^ j)
```

并给出:对**任意**紧自伴 + HS 型 T(含 B),完备特征族 + `exists_multiplicity_enumeration`
(FrozenSpectralCount,仅需紧性)⇒ 满足上述 hdiag/hmult 的 (val, vec) 存在
——M1-D 消费这条组合。对角和一律以 `HasSum` + 已证可和性陈述,**不得**把非可和
tsum 的 Lean 默认值当作结论。

## 5. M1-D 最小接口(主 agent 已准备;依赖 A/B/C 通过后接入执行)

关键路线简化(比 23:A8/A9 的通用 k-Fubini 更省):**B^k 的对角和经"配对循环性"移到
`(W∘T)^k` 的对角和,而 `W∘T = TOp(rieszKernel psi c omega)`(左乘 ω(x) 是核运算!)**,
于是识别链全部落在已落地工具上:`TOp_compPowR`(核算子幂=复合核,TOpComposition)、
`tracePair_comp_tsum`(2 因子对角和=cycle2,TensorParsevalTracePair)、
`weightedRieszCycleIntegral_eq_kernelProd`(加权循环积分认同)。

### M1-D1(模块 `Hurst/TracePairCycle.lean`,抽象层,无核依赖)

```lean
/-- 配对循环性:HS 型复合的对角和可交换(基不变框架;证明走 Parseval 双展开 +
    绝对可和,复用 EigenTraceBridge/TensorParsevalTracePair 的可和性模式)。 -/
theorem tracePair_cyclic {U V : L2 →L[ℝ] L2} (e : HilbertBasis ℕ ℝ L2)
    (hU : HS 型条件:∀ e', Summable (fun p => ⟪e' p.1, U (e' p.2)⟫²) 且有一致界)
    (hV : 同上) (hUV : U∘V 与 V∘U 的同款条件) :
    (∑' i, inner ℝ (e i) (U (V (e i)))) = (∑' i, inner ℝ (e i) (V (U (e i))))
```

### M1-D2(模块 `Hurst/EquivalentKernelSpectrum.lean`)

```lean
/-- 左乘即核运算:M_ω ∘ TOp K = TOp (fun p => omega p.1 * K p)。 -/
theorem mulOperator_comp_TOp {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) {K : ℝ × ℝ → ℝ} (hKm : Measurable K)
    (hK : HSKernel K) (hK' : HSKernel (fun p => omega p.1 * K p)) :
    (mulOperator omega hm hess).comp (TOp K hK) = TOp (fun p => omega p.1 * K p) hK'

/-- 主桥:B 的谱幂对角和 = 加权循环积分(k ≥ 2;基不变由 M1-C,hc/hpsi 系 capstone 数据)。 -/
theorem diagSum_B_eq_weightedCycle (psi c : ℝ) (hc : 0 < c) (hpsi0 : 0 < psi)
    (hpsi2 : 2 * psi < 1) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (k : ℕ) (hk : 2 ≤ k) (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ e i ((B psi c omega hpsi0 hpsi2 hc) ^ k) (e i))
      = Hurst.weightedRieszCycleIntegral k psi c omega
-- 路线:
-- step1(算子恒等式): B^k = S ∘ (W∘T)^{k-1} ∘ W ∘ S   [B = S∘W∘S, S² = T,归纳]
-- step2(循环性): Diag(B^k) = Diag((W∘T)^k)            [tracePair_cyclic × k;两个 S 移位;
--        S 的 HS 型条件由 A7 的矩阵界 + ∑κ² 供给]
-- step3(核化):   W∘T = TOp (rieszKernel psi c omega)   [mulOperator_comp_TOp;
--        rieszKernel psi c omega 的 HSKernel 已落地]
-- step4(k 步迭代): Diag((TOp C)^k) = cycle2 C (compPowR (k-2) C)
--        [tracePair_comp_tsum × (k-2) 迭代 + TOp_compPowR / compKernel 结合,已落地]
-- step5(认同):     = weightedRieszCycleIntegral k psi c omega
--        [weightedRieszCycleIntegral_eq_kernelProd + rieszCycleIntegrand_eq,已落地;
--         k=2 锚:cycle2_rieszKernel_eq_weighted]

/-- 最终组装:B 的谱枚举即实际带权 Riesz 谱(审查阻断 1 的直接消除)。 -/
theorem exists_weightedRieszSpectrum_min (psi c : ℝ) (hc : 0 < c) (hpsi0 : 0 < psi)
    (hpsi2 : 2 * psi < 1) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    ∃ (val : ℕ → ℝ) (vec : ℕ → L2),
      IsDiagEnum (B …).toLin' val vec ∧ (多重性子句,exists_diag_enumeration_clm 形态)
      ∧ Summable (fun j => val j ^ 2)
      ∧ ∀ k : ℕ, 2 ≤ k → HasSum (fun j => val j ^ k)
          (Hurst.weightedRieszCycleIntegral k psi c omega)
-- 路线:C 的 exists_diag_enumeration_clm(作用于 B,HS 条件由 A7 供给)+
--       hBridge_clm(基不变)+ diagSum_B_eq_weightedCycle 合成。
-- omega := equivalentKernel r 实例:hm/hess 由 continuous/bounded 落地定理消解。
```

### 分工与缺口登记

- M1-D1(tracePair_cyclic):新分析,复用 H/E 可和性模式;先行派发(不依赖 A/B/C)。
- M1-D2:依赖 A(正性+特征族)、B(S 与 B 的绑定 + A7)、C(hBridge_clm + 枚举存在)。
- **已登记缺口**(完成前不算 M1 验收):step1 的归纳细节;step2 中 S 的 HS 型条件从
  A7 矩阵界到"任意基"的转写;`Summable (val²)` 从 A7 的显式推导;
  `exists_weightedRieszSpectrum_min` 的 equivalentKernel 实例化。
- Hilbert 基 `e` 仍是环境参数(内部待证事项,见 §1)。

## 6. 验收标准(M1)

1. A/B/C/D 四模块全部编译零错误、零 sorry;`#print axioms` 仅基础三条。
2. `exists_weightedRieszSpectrum` 以 `omega := equivalentKernel r`(固定 r,如 r=1)
   完整实例化——即审查阻断 1 的直接消除。
3. 聚合 import + `lake build` + AxiomAudit 追加 + 三件套重生成;`VALIDATION_PROGRESS.md`
   同步更新(含仍缺清单)。
4. 旧 `rieszSpectrumVal_hGen`/`*_v3_closed` **保留不删**(组合结构可复用),但其文档
   必须注明"hconst 前提不可满足,实际模型走 EquivalentKernelSpectrum 线"(修复状态
   传播,不伪装)。
