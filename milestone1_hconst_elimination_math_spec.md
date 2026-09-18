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

## 5. M1-D(收口路线,**草案——非冻结签名**;A/B/C 落地后先写可检查的最小接口再派发)

> ⚠️ 本节当前是路线描述,含伪代码占位(如 hconst'、省略号),**不是**冻结 Lean 签名。
> M1-D 派发前必须产出:构造 B 的显式接口、真实谱枚举、k=2 与所有 k≥3 的分离定理、
> 可满足实例(ω = equivalentKernel r 固定 r)。阶段性缺口记录在案但不算 M1 验收通过。
> Hilbert 基存在也是内部待证事项(见 §1 表格)。

目标定理(模块 `Hurst/EquivalentKernelSpectrum.lean`):

```lean
/-- W6(19)/A6(A10)的最终形态:B 的谱是实际带权 Riesz 谱。 -/
theorem exists_weightedRieszSpectrum (r : ℕ) (psi c : ℝ)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable (equivalentKernel r))
    (hbdd : ∀ x, |equivalentKernel r x| ≤ MR)  -- 由 equivalentKernel_bounded 具体化
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst' : ∀ x y : ℝ, …)  -- 不再需要!
    (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1) :
    ∃ (val : ℕ → ℝ) (vec : ℕ → L2),
      IsDiagEnum … ∧ (多重性子句) ∧ Summable (fun j => val j ^ 2)
      ∧ ∀ k : ℕ, 2 ≤ k → HasSum (fun j => val j ^ k)
          (Hurst.weightedRieszCycleIntegral k psi c (equivalentKernel r))
```

路线(全部已在既有工具上有先例):
1. M1-B 的 B(自伴紧,以 A7 界保证谱平方可和);M1-C 的组合给出 (val, vec) +
   `∀ j ≥ 2 ∀ 基,∑⟪B^j e,e⟫ = ∑' val^j`(基不变)。
2. **在 K-特征基处求值**(基不变 ⇒ 可选最方便的基):
   `∑_{i₁..i_k} ∏_j κ_{i_j}·⟪v_{i_j}, W v_{i_{j+1}}⟫ = J_k^ω`
   ——核展开 `K = ∑ κ v⊗v`(L² 收敛,`kernel_inner_eq_tsum_prodKernel` 已落地)+
   k-Fubini(绝对收敛由 A7 的 AM–GM 支配,E/H 的可和性模式)。
3. `tr(B^k) = tr((WK)^k)` 循环移位:A8 的矩阵幂对角恒等式
   (B 的矩阵 `b_ij = √(κ_iκ_j)⟪v_i, W v_j⟫`;循环乘积 ∏√(κκ) = ∏κ)。
4. `J_k^ω = weightedRieszCycleIntegral k psi (equivalentKernel r)`:
   现有 `weightedRieszCycleIntegral_eq_kernelProd` + `rieszCycleIntegrand_eq`(已落地)。
5. k=2 锚:`∑' μ² = ‖B‖²_HS` 型(基无关对角和)+ 与 hTwo 型 Parseval 对齐(若 B 侧
   无法直接对齐 J_2,允许 M1-D 首版先交付 k ≥ 3 并把 k=2 列为缺口——**须显式声明**)。

**列清仍缺什么(预期)**:k-重张量 Parseval 的 Fubini 支配(E 的 2-重 → k-重的推广,
或经 `kernel_inner_eq_tsum_prodKernel` 的迭代);矩阵幂对角恒等式的无限维版本
(有限秩逼近 + A4 型望远镜估计);若 Γ 表示在 mathlib 缺名,M1-A 内自证。

## 6. 验收标准(M1)

1. A/B/C/D 四模块全部编译零错误、零 sorry;`#print axioms` 仅基础三条。
2. `exists_weightedRieszSpectrum` 以 `omega := equivalentKernel r`(固定 r,如 r=1)
   完整实例化——即审查阻断 1 的直接消除。
3. 聚合 import + `lake build` + AxiomAudit 追加 + 三件套重生成;`VALIDATION_PROGRESS.md`
   同步更新(含仍缺清单)。
4. 旧 `rieszSpectrumVal_hGen`/`*_v3_closed` **保留不删**(组合结构可复用),但其文档
   必须注明"hconst 前提不可满足,实际模型走 EquivalentKernelSpectrum 线"(修复状态
   传播,不伪装)。
