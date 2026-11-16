module

public import FiniteCore
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem unnormalized_gibbs
    {I : Type*} [Fintype I] (x w : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hw : ∀ i, 0 ≤ w i)
    (hX : 0 < ∑ i, x i) (hW : 0 < ∑ i, w i)
    (hsupport : ∀ i, 0 < x i → 0 < w i) :
    (∑ i, x i) * Real.log (∑ i, x i) - (∑ i, x i * Real.log (x i)) ≤
      -(∑ i, x i * Real.log (w i)) + (∑ i, x i) * Real.log (∑ i, w i) := by
  let S : ℝ := ∑ i, x i
  have hS : 0 < S := hX
  let p : I → ℝ := fun i => x i / S
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hx i) hS.le
  have hpsum : ∑ i, p i = 1 := by
    simp only [p, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hS.ne'
  have hpsupport : ∀ i, 0 < p i → 0 < w i := by
    intro i hi
    exact hsupport i ((div_pos_iff_of_pos_right hS).mp hi)
  have hg := finite_gibbs p w hp hw hpsum hpsupport hW
  have hid : (∑ i, p i * Real.log (p i)) =
      ((∑ i, x i * Real.log (x i)) - S * Real.log S) / S := by
    calc
      (∑ i, p i * Real.log (p i)) =
          ∑ i, (x i * Real.log (x i) - x i * Real.log S) / S := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x i = 0
        · simp [p,hi]
        · dsimp [p]
          rw [Real.log_div hi hS.ne']
          ring
      _ = _ := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib]
        rfl
  have href : (∑ i, p i * Real.log (w i)) = (∑ i, x i * Real.log (w i)) / S := by
    simp only [p, div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid,href] at hg
  have hm := mul_le_mul_of_nonneg_right hg hS.le
  simp only [add_mul,neg_mul,div_mul_cancel₀ _ hS.ne'] at hm
  change S * Real.log S - (∑ i, x i * Real.log (x i)) ≤ _
  nlinarith

theorem weighted_log_sum
    {I : Type*} (P : Finset I) (x w : I → ℝ)
    (hP : P.Nonempty) (hx : ∀ i ∈ P, 0 < x i) (hw : ∀ i ∈ P, 0 < w i) :
    (∑ i ∈ P, x i) * Real.log (∑ i ∈ P, x i) - (∑ i ∈ P, x i * Real.log (x i)) ≤
      -(∑ i ∈ P, x i * Real.log (w i)) + (∑ i ∈ P, x i) * Real.log (∑ i ∈ P, w i) := by
  have : Nonempty P := let ⟨i,hi⟩ := hP; ⟨⟨i,hi⟩⟩
  have hX : (0 : ℝ) < ∑ i : P, x i :=
    Finset.sum_pos (fun i _ => hx i i.property) Finset.univ_nonempty
  have hW : (0 : ℝ) < ∑ i : P, w i :=
    Finset.sum_pos (fun i _ => hw i i.property) Finset.univ_nonempty
  have h := unnormalized_gibbs (fun i : P => x i) (fun i : P => w i)
    (fun i => (hx i i.property).le) (fun i => (hw i i.property).le)
    hX hW (fun i _ => hw i i.property)
  have hxl : (∑ i : P, x i * Real.log (x i)) = ∑ i ∈ P, x i * Real.log (x i) :=
    Finset.sum_coe_sort P (fun i => x i * Real.log (x i))
  have hxw : (∑ i : P, x i * Real.log (w i)) = ∑ i ∈ P, x i * Real.log (w i) :=
    Finset.sum_coe_sort P (fun i => x i * Real.log (w i))
  rw [hxl,hxw] at h
  simpa only [Finset.sum_coe_sort] using h

/-- Regroup a finite weighted sum by the values of a coordinate. -/
theorem sum_by_coordinate {A B : Type*} [DecidableEq B]
    (S : Finset A) (f : A → B) (F : B → A → ℝ) :
    (∑ x ∈ S, F (f x) x) =
      ∑ v ∈ S.image f, ∑ x ∈ S.filter (fun x => f x = v), F v x := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f) (g := f)
    (fun x hx => mem_image_of_mem _ hx)]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · rw [h]
  · rfl

end LatinonEntropy

#print axioms LatinonEntropy.weighted_log_sum
