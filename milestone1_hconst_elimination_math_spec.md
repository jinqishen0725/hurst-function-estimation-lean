# 里程碑 1 数学契约:消除 hconst 的真实等价核谱对象与循环积分桥

日期:2026-09-18。依据:审查阻断 1(`verification/Session3PremiseAudit.lean` 已 Lean 证明
hconst 不可满足)、书面方案 22:W6 与 23:A4–A6。本契约冻结定理签名;任何偏差必须
声明式回写本文件与 `VALIDATION_PROGRESS.md`。

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
| W 有界自伴 | 新小引理:`ω` 可测有界 ⇒ `M_ω : L2 →L[ℝ] L2`、`IsSymmetric`、`‖M_ω‖ ≤ MR` | 🆕 M1-B(机械) |
| K 非负(κ_i ≥ 0) | A5 Laplace/Γ 表示 + **已落地** `HS.kernelPSD_exp_dist`(e^{-u\|x−y\|} PSD,u>0)的混合 | 🆕 M1-A(核心难点) |
| K 紧 | HS 核算子紧性:沿用 `isCompactOperator_TOp_riesz`(RieszCompactEnumeration:95)的证明骨架(该证明不依赖 ω/常数性) | 🆕 M1-A(骨架复用) |
| Hilbert 基 `e`(环境数据) | 现有 idiom(与 hBridge/tracePair_comp_tsum 相同);结论与 e 无关 | ✅ 环境数据 |

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

/-- A5:无权 Riesz 算子非负(Laplace/Γ 表示 + exp-核 PSD 混合)。 -/
theorem inner_TOp_unweightedRiesz_nonneg {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (f : L2) :
    0 ≤ inner ℝ (TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) f) f

/-- 完备非负特征族(K 的;κ ≥ 0 由非负性 + 特征方程)。 -/
theorem exists_nonneg_eigenfamily {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1) :
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
/-- 有界可测乘法算子。 -/
def mulOperator (omega : ℝ → ℝ) : L2 →L[ℝ] L2   -- 构造方式不限(简单函数稠密/直接定义)
theorem mulOperator_symm {omega : ℝ → ℝ} (hm : Measurable omega) :
    (↑(mulOperator omega) : L2 →ₗ[ℝ] L2).IsSymmetric
theorem norm_mulOperator_le {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hbdd : ∀ x, |omega x| ≤ MR) : ‖mulOperator omega‖ ≤ MR

/-- 正自伴紧算子在完备非负特征族上的正平方根(定义在特征族上,Parseval 收敛)。 -/
theorem exists_positive_sqrt {T : L2 →L[ℝ] L2}
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i) :
    ∃ S : L2 →L[ℝ] L2, (↑S : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ (∀ i, S (v i) = Real.sqrt (κ i) • v i)
      ∧ ∀ x, S (S x) = T x
      ∧ ∀ i, ‖S (v i)‖ = 1 ∨ S (v i) = 0   -- 由 √κ 定义直接成立(可省)

/-- A7:B = S ∘ M_ω ∘ S 自伴且 HS 型矩阵界(给 M1-D 的绝对可和性输入)。 -/
theorem exists_B_selfAdjoint_hs {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hbdd : ∀ x, |omega x| ≤ MR)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp (unweightedRieszKernel psi c) hK (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) :
    ∃ B : L2 →L[ℝ] L2, (↑B : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ ∃ C : ℝ, (∀ i j, |inner ℝ (e i) (B (e j))| 的平方双重和 ≤ C)  -- A7:对任意 ON 基 e
```

(签名细化权在 M1-B 执行者,但:①B 的对称性、②A7 双平方和界 `≤ ‖ω‖∞²·∑κ²`、
③`B (v i)` 的 `√(κ_iκ_j)`-矩阵结构(⟪v_i, B v_j⟫ = √(κ_iκ_j)·⟪v_i, W v_j⟫)必须作为
命名定理可独立消费——M1-D 依赖这三件。)

## 4. 冻结接口(M1-C → M1-D)

模块 `Hurst/EndLevelTraceBridge.lean`(namespace HS):把 `EigenTraceBridge.hBridge`
从"核算子 `TOp K hK`"泛化到"抽象紧自伴 CLM/End"(H 的证明只用了算子结构):

```lean
theorem hBridge_clm {T : L2 →L[ℝ] L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hTcompact : IsCompactOperator T)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hdiag : IsDiagEnum (T.toLin') val vec)      -- 与既有 IsDiagEnum 的 End/CLM 对齐
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (T.toLin') μ → μ ≠ 0 →
      Nat.card {m : ℕ // val m = μ} = Module.finrank ℝ (Module.End.eigenspace (T.toLin') μ))
    (j : ℕ) (hj : 2 ≤ j) (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ ((T ^ j) (e i)) (e i)) = ∑' m : ℕ, val m ^ j
```

并给出:对**任意**紧自伴 T(含 B),完备特征族 + `exists_multiplicity_enumeration`
(FrozenSpectralCount,仅需紧性)⇒ 满足上述 hdiag/hmult 的 (val, vec) 存在
——M1-D 消费这条组合。

## 5. M1-D(本里程碑的收口,契约先行;A/B/C 落地后派发)

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
