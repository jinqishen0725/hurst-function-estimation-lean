import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

noncomputable section
open scoped RealInnerProductSpace
namespace Hurst

theorem hilbert_diagonal_inner_basis {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : HilbertBasis ℕ ℝ E) (L R : E →L[ℝ] F) (d : ℕ → ℝ)
    (h : ∀ n m, ⟪L (b n),R (b m)⟫ = if n=m then d n else 0) (f : E) (m : ℕ) :
    ⟪L f,R (b m)⟫ = d m*⟪b m,f⟫ := by
  have he := (b.hasSum_repr f).mapL ((innerSL ℝ (R (b m))).comp L)
  have hid : (fun n => ((innerSL ℝ (R (b m))).comp L) (b.repr f n • b n)) =
      fun n => if n=m then d m*⟪b m,f⟫ else 0 := by
    funext n
    simp only [ContinuousLinearMap.comp_apply,map_smul,innerSL_apply_apply,inner_smul_right,
      b.repr_apply_apply,smul_eq_mul]
    rw [← real_inner_comm (R (b m)) (L (b n)),h n m]
    split_ifs with hnm
    · subst m
      ring
    · ring
  rw [hid] at he
  have hz : HasSum (fun n : ℕ => if n=m then d m*⟪b m,f⟫ else 0) (d m*⟪b m,f⟫) :=
    hasSum_ite_eq m _
  have hr := he.unique hz
  simpa only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm] using hr

theorem hilbert_diagonal_inner_expansion {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : HilbertBasis ℕ ℝ E) (L R : E →L[ℝ] F) (d : ℕ → ℝ)
    (h : ∀ n m, ⟪L (b n),R (b m)⟫ = if n=m then d n else 0) (f g : E) :
    HasSum (fun n => d n*⟪b n,f⟫*⟪b n,g⟫) ⟪L f,R g⟫ := by
  have he := (b.hasSum_repr g).mapL ((innerSL ℝ (L f)).comp R)
  convert he using 1 <;> first | rfl |
    (funext n
     simp only [ContinuousLinearMap.comp_apply,map_smul,innerSL_apply_apply,inner_smul_right,
       smul_eq_mul,b.repr_apply_apply,hilbert_diagonal_inner_basis b L R d h]
     ring)

end Hurst
