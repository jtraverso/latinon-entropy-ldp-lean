module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
Finite deterministic ingredients for the proposed Latinon entropy proof.

This file does not assert existence of the residual potential certificate,
the correction optimizer, the row process, or the Latinon LDP. It proves the
cost implication from a certificate and the finite Gibbs entropy inequality.
-/

noncomputable section

namespace LatinonEntropy

open Finset

theorem abs_le_mul_gap {d g : ℝ}
    (hpos : 0 < d → 1 ≤ g) (hneg : d < 0 → g ≤ -1) : |d| ≤ d * g := by
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd]
    by_cases hz : d = 0
    · simp [hz]
    · have hg := hpos (lt_of_le_of_ne hd (Ne.symm hz))
      nlinarith
  · have hd' : d < 0 := lt_of_not_ge hd
    rw [abs_of_neg hd']
    have hg := hneg hd'
    nlinarith

/-- A bounded vertex potential certificate bounds transportation correction
cost by the sum of row and column defects. This is a certificate implication,
not the missing assertion that such potentials exist. -/
theorem correction_cost_of_potentials
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (D : Y → Z → ℝ) (u : Y → ℝ) (v : Z → ℝ) (L : ℝ)
    (hu : ∀ y, |u y| ≤ L) (hv : ∀ z, |v z| ≤ L)
    (hgap : ∀ y z, |D y z| ≤ D y z * (v z - u y)) :
    (∑ y, ∑ z, |D y z|) ≤
      L * ((∑ y, |∑ z, D y z|) + ∑ z, |∑ y, D y z|) := by
  have pairing :
      (∑ y, ∑ z, D y z * (v z - u y)) =
        (∑ z, v z * ∑ y, D y z) - ∑ y, u y * ∑ z, D y z := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    all_goals apply Finset.sum_congr rfl; intro j hj; ring
  calc
    (∑ y, ∑ z, |D y z|) ≤ ∑ y, ∑ z, D y z * (v z - u y) :=
      Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ => hgap y z
    _ = (∑ z, v z * ∑ y, D y z) - ∑ y, u y * ∑ z, D y z := pairing
    _ ≤ (∑ z, |v z| * |∑ y, D y z|) + ∑ y, |u y| * |∑ z, D y z| := by
      have hc : (∑ z, v z * ∑ y, D y z) ≤ ∑ z, |v z| * |∑ y, D y z| := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [abs_mul] using le_abs_self (v z * ∑ y, D y z)
      have hr : -(∑ y, u y * ∑ z, D y z) ≤ ∑ y, |u y| * |∑ z, D y z| := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro y _
        simpa only [abs_mul] using neg_le_abs (u y * ∑ z, D y z)
      linarith
    _ ≤ (∑ z, L * |∑ y, D y z|) + ∑ y, L * |∑ z, D y z| := by
      exact add_le_add
        (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hv z) (abs_nonneg _))
        (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hu y) (abs_nonneg _))
    _ = L * ((∑ y, |∑ z, D y z|) + ∑ z, |∑ y, D y z|) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- The exact L1 cost conclusion for matrices with corrected unit margins. -/
theorem correction_cost_unit_margins
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (M Q : Y → Z → ℝ) (u : Y → ℝ) (v : Z → ℝ)
    (hu : ∀ y, |u y| ≤ 3) (hv : ∀ z, |v z| ≤ 3)
    (hrow : ∀ y, ∑ z, Q y z = 1) (hcol : ∀ z, ∑ y, Q y z = 1)
    (hup : ∀ y z, Q y z < M y z → v z - u y ≤ -1)
    (hdown : ∀ y z, M y z < Q y z → 1 ≤ v z - u y) :
    (∑ y, ∑ z, |Q y z - M y z|) ≤
      3 * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  have h := correction_cost_of_potentials (fun y z => Q y z - M y z) u v 3 hu hv
    (fun y z => abs_le_mul_gap
      (fun hd => hdown y z (sub_pos.mp hd))
      (fun hd => hup y z (sub_neg.mp hd)))
  simpa only [Finset.sum_sub_distrib, hrow, hcol, abs_sub_comm] using h

/-- Gibbs' inequality with nonnormalized nonnegative reference weights.
Zero coordinates of the probability vector are allowed. -/
theorem finite_gibbs
    {I : Type*} [Fintype I] (p w : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hp_sum : ∑ i, p i = 1)
    (hw_support : ∀ i, 0 < p i → 0 < w i)
    (hw_sum : 0 < ∑ i, w i) :
    -(∑ i, p i * Real.log (p i)) ≤
      -(∑ i, p i * Real.log (w i)) + Real.log (∑ i, w i) := by
  let S : ℝ := ∑ i, w i
  have hS : 0 < S := hw_sum
  have step : ∀ i,
      p i * (Real.log (w i) - Real.log (p i) - Real.log S) ≤ w i / S - p i := by
    intro i
    by_cases hz : p i = 0
    · simp only [hz, zero_mul, sub_zero]
      exact div_nonneg (hw i) hS.le
    · have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hwi : 0 < w i := hw_support i hpi
      have h := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hwi (mul_pos hpi hS))) hpi.le
      rw [Real.log_div hwi.ne' (mul_pos hpi hS).ne', Real.log_mul hpi.ne' hS.ne'] at h
      have heq : p i * (w i / (p i * S) - 1) = w i / S - p i := by
        field_simp [hpi.ne', hS.ne']
      rw [heq] at h
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => step i)
  have hid : (∑ i, p i * (Real.log (w i) - Real.log (p i) - Real.log S)) =
      (∑ i, p i * Real.log (w i)) - (∑ i, p i * Real.log (p i)) - Real.log S := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
  have hr : (∑ i, (w i / S - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp_sum]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    change S * S⁻¹ - 1 = 0
    simp [hS.ne']
  rw [hid, hr] at hs
  change -(∑ i, p i * Real.log (p i)) ≤
    -(∑ i, p i * Real.log (w i)) + Real.log S
  linarith

/-- The blockwise entropy maximum at fixed total mass. Zero mass and zero
entries are included. This supplies the Jensen step in the block upper bound. -/
theorem block_entropy_le_uniform
    {I : Type*} [Fintype I] [Nonempty I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    -(∑ i, x i * Real.log (x i)) ≤
      (∑ i, x i) * (Real.log (Fintype.card I) - Real.log (∑ i, x i)) := by
  let S : ℝ := ∑ i, x i
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hx i)
  by_cases hz : S = 0
  · have hzero : ∀ i, x i = 0 := by
      intro i
      have hi : x i ≤ S := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (by linarith) (hx i)
    simp [hzero]
  · have hS : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hz)
    let p : I → ℝ := fun i => x i / S
    have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (hx i) hS.le
    have hp_sum : ∑ i, p i = 1 := by
      simp only [p, div_eq_mul_inv, ← Finset.sum_mul]
      change S * S⁻¹ = 1
      exact mul_inv_cancel₀ hS.ne'
    have hn : (0 : ℝ) < ∑ _i : I, (1 : ℝ) := by
      simpa using (Nat.cast_pos.mpr (Fintype.card_pos) : (0 : ℝ) < Fintype.card I)
    have hg := finite_gibbs p (fun _ => 1) hp (fun _ => zero_le_one)
      hp_sum (fun _ _ => zero_lt_one) hn
    simp only [Real.log_one, mul_zero, Finset.sum_const_zero, neg_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at hg
    have hid : (∑ i, p i * Real.log (p i)) =
        ((∑ i, x i * Real.log (x i)) - S * Real.log S) / S := by
      calc
        (∑ i, p i * Real.log (p i)) =
            ∑ i, (x i * Real.log (x i) - x i * Real.log S) / S := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hxi : x i = 0
          · simp [p, hxi]
          · dsimp [p]
            rw [Real.log_div hxi hS.ne']
            ring
        _ = ((∑ i, x i * Real.log (x i)) - S * Real.log S) / S := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib]
          rfl
    rw [hid] at hg
    have hh : -((∑ i, x i * Real.log (x i)) - S * Real.log S) ≤
        Real.log (Fintype.card I) * S :=
      (div_le_iff₀ hS).mp (by simpa only [neg_div] using hg)
    change -(∑ i, x i * Real.log (x i)) ≤
      S * (Real.log (Fintype.card I) - Real.log S)
    nlinarith

end LatinonEntropy

#print axioms LatinonEntropy.correction_cost_unit_margins
#print axioms LatinonEntropy.finite_gibbs
#print axioms LatinonEntropy.block_entropy_le_uniform
