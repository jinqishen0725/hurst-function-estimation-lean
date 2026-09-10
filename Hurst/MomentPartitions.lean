import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

noncomputable section
open Set
namespace Hurst

def MomentPattern (m : ℕ) :=
  Σ v : Fin (m+1), {f : Fin m → Fin v.val // Function.Surjective f}

instance (m : ℕ) : Fintype (MomentPattern m) := by
  unfold MomentPattern
  infer_instance

def MomentRealization (m : ℕ) (ι : Type*) :=
  Σ q : MomentPattern m, Fin q.1.val ↪ ι

instance (m : ℕ) (ι : Type*) [Fintype ι] : Fintype (MomentRealization m ι) := by
  unfold MomentRealization
  infer_instance

def momentRealizationTuple {m : ℕ} {ι : Type*} (z : MomentRealization m ι) : Fin m → ι :=
  fun i => z.2 (z.1.2.val i)

theorem momentRealizationTuple_surjective (m : ℕ) (ι : Type*) [Fintype ι] :
    Function.Surjective (@momentRealizationTuple m ι) := by
  classical
  intro t
  let e := Fintype.equivFin (Set.range t)
  let v : Fin (m+1) := ⟨Fintype.card (Set.range t),by
    have h := Fintype.card_range_le t
    simp only [Fintype.card_fin] at h
    omega⟩
  let f : Fin m → Fin v.val := e ∘ Set.rangeFactorization t
  have hf : Function.Surjective f := e.surjective.comp Set.rangeFactorization_surjective
  let g : Fin v.val ↪ ι :=
    ⟨fun i => (e.symm i).val,Subtype.val_injective.comp e.symm.injective⟩
  refine ⟨⟨⟨v,f,hf⟩,g⟩,?_⟩
  funext i
  exact congrArg Subtype.val (e.symm_apply_apply (Set.rangeFactorization t i))

def momentMultiplicity {m : ℕ} (q : MomentPattern m) (j : Fin q.1.val) : ℕ :=
  Fintype.card {i : Fin m // q.2.val i=j}

theorem momentMultiplicity_pos {m : ℕ} (q : MomentPattern m) (j : Fin q.1.val) :
    0<momentMultiplicity q j := by
  classical
  obtain ⟨i,hi⟩ := q.2.property j
  exact Fintype.card_pos_iff.mpr ⟨⟨i,hi⟩⟩

theorem momentMultiplicity_sum {m : ℕ} (q : MomentPattern m) :
    ∑ j,momentMultiplicity q j=m := by
  classical
  have h := Fintype.sum_fiberwise' q.2.val (fun _ => (1:ℕ))
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_fin,momentMultiplicity] using h

theorem momentMultiplicity_singletons_bound {k : ℕ} (q : MomentPattern (2*k)) :
    2*q.1.val ≤ 2*k + (Finset.univ.filter (fun j => momentMultiplicity q j=1)).card := by
  classical
  have hp := momentMultiplicity_pos q
  have hsum := momentMultiplicity_sum q
  have hi : ∑ j : Fin q.1.val,(2:ℕ) ≤ ∑ j,(momentMultiplicity q j+if momentMultiplicity q j=1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs with h
    · omega
    · have := hp j; omega
  simpa [Finset.sum_add_distrib,Finset.sum_boole,hsum,Nat.mul_comm] using hi

theorem momentRealization_product {m : ℕ} {ι R : Type*} [CommMonoid R]
    (z : MomentRealization m ι) (Y : ι → R) :
    (∏ i : Fin m,Y (momentRealizationTuple z i)) =
      ∏ j : Fin z.1.1.val,Y (z.2 j)^momentMultiplicity z.1 j := by
  classical
  have h := Fintype.prod_fiberwise' z.1.2.val (fun j => Y (z.2 j))
  simpa only [Finset.prod_const,Finset.card_univ,momentMultiplicity,momentRealizationTuple] using h.symm

theorem moment_tuple_sum_le_realizations {m : ℕ} {ι : Type*} [Fintype ι]
    (F : (Fin m → ι) → ℝ) (hF : ∀ t,0≤F t) :
    (∑ t,F t) ≤ ∑ z : MomentRealization m ι,F (momentRealizationTuple z) := by
  classical
  have he : Finset.univ.image (@momentRealizationTuple m ι)=Finset.univ := by
    ext t
    simpa only [Finset.mem_image,Finset.mem_univ,true_and,iff_true] using momentRealizationTuple_surjective m ι t
  have hh := Finset.sum_image_le_of_nonneg (s:=Finset.univ) (g:=@momentRealizationTuple m ι)
    (f:=F) (fun t _ => hF t)
  rwa [he] at hh

end Hurst
