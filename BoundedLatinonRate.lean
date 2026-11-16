module

public import LatinonFullDyadicKL

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical

theorem positive_profile_density_divergence_le_log_b {n : ℕ} (P : PositiveLatinProfile n) :
    -latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z) ≤ Real.log P.b := by
  let f := fun x y z : Fin n => (n : ℝ)*P.p x y z
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hpos : ∀ x y z, 0 < f x y z := fun x y z => mul_pos hnR (P.entry_pos x y z)
  have hupper : ∀ x y z, f x y z ≤ P.b := by
    intro x y z
    have hh := mul_le_mul_of_nonneg_left (P.bounds x y z).2 hnR.le
    rwa [mul_div_cancel₀ _ hnR.ne'] at hh
  have htotal : (∑ x, ∑ y, ∑ z, f x y z) = (n : ℝ)^3 := by
    dsimp only [f]
    simp only [← mul_sum,P.row_mass,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    ring
  have hsum : (∑ x, ∑ y, ∑ z, f x y z*Real.log (f x y z)) ≤
      (n : ℝ)^3*Real.log P.b := by
    calc
      (∑ x, ∑ y, ∑ z, f x y z*Real.log (f x y z)) ≤
          ∑ x, ∑ y, ∑ z, f x y z*Real.log P.b := by
        apply sum_le_sum
        intro x _
        apply sum_le_sum
        intro y _
        apply sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos x y z) (hupper x y z)) (hpos x y z).le
      _ = (n : ℝ)^3*Real.log P.b := by
        simpa only [Finset.sum_mul] using congrArg (fun r : ℝ => r*Real.log P.b) htotal
  change -(-(∑ x, ∑ y, ∑ z, f x y z*Real.log (f x y z))/(n : ℝ)^3) ≤ _
  rw [neg_div,neg_neg]
  apply (div_le_iff₀ (pow_pos hnR 3)).mpr
  nlinarith only [hsum]

theorem bounded_latinon_rate_le_log (W : LatinonMeasure) (a b : ℝ) (ha : 0 < a)
    (h : HasLatinonDensityBounds W a b) : latinonRate W ≤ ENNReal.ofReal (Real.log b) := by
  rw [latinon_rate_eq_iSup_dyadic W]
  apply iSup_le
  intro k
  rw [latinon_grid_table_entropy_eq_density W (dyadicGridSize_pos k)]
  apply ENNReal.ofReal_le_ofReal
  exact positive_profile_density_divergence_le_log_b
    (boundedLatinonGridProfile W a b ha h (dyadicGridSize k) (dyadicGridSize_pos k))

theorem bounded_latinon_rate_ne_top (W : LatinonMeasure) (a b : ℝ) (ha : 0 < a)
    (h : HasLatinonDensityBounds W a b) : latinonRate W ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_latinon_rate_le_log W a b ha h)

end LatinonEntropy

#print axioms LatinonEntropy.positive_profile_density_divergence_le_log_b
#print axioms LatinonEntropy.bounded_latinon_rate_le_log
#print axioms LatinonEntropy.bounded_latinon_rate_ne_top
