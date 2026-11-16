module

public import FluidStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem finite_defect_gronwall (D : ℕ → ℝ) (A b B L : ℝ) (T : ℕ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L) (hD : ∀ t, 0 ≤ D t)
    (hrec : ∀ t ≤ T, D t ≤ A+b*(∑ s ∈ range t, (B+L*D s)))
    (t : ℕ) (ht : t ≤ T) :
    D t ≤ (A+(t : ℝ)*b*B)*Real.exp ((t : ℝ)*b*L) := by
  let E : ℕ → ℝ := fun s => if s ≤ T then D s else 0
  have hE : ∀ s, 0 ≤ E s := by
    intro s
    by_cases hs : s ≤ T
    · simpa only [E,hs,ite_true] using hD s
    · simp only [E,hs,ite_false,le_refl]
  have hrecE : ∀ k, E k ≤ A+b*(∑ s ∈ range k, (B+L*E s)) := by
    intro k
    by_cases hk : k ≤ T
    · have he : (∑ s ∈ range k, (B+L*E s)) = ∑ s ∈ range k, (B+L*D s) := by
        apply sum_congr rfl
        intro s hs
        have hsT : s ≤ T := (le_of_lt (mem_range.mp hs)).trans hk
        simp only [E,hsT,ite_true]
      rw [he]
      simpa only [E,hk,ite_true] using hrec k hk
    · have he : E k = 0 := by simp only [E,hk,ite_false]
      rw [he]
      exact add_nonneg hA (mul_nonneg hb (sum_nonneg (fun s _ => add_nonneg hB (mul_nonneg hL (hE s)))))
  have hg := defect_gronwall E A b B L hA hb hB hL hrecE t
  simpa only [E,ht,ite_true] using hg

theorem total_coordinate_noise_le (n T : ℕ) (hn : 0 < n) (hT : T ≤ n)
    (c : ℝ) (hc : 0 ≤ c) :
    2*(n : ℝ)*Real.sqrt ((T : ℝ)*(c/n)^2) ≤ 2*c*Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.sqrt_mul (Nat.cast_nonneg T),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (div_nonneg hc hnR.le)]
  calc
    _ = 2*c*Real.sqrt (T : ℝ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hT)) (mul_nonneg (by norm_num) hc)

end LatinonEntropy

#print axioms LatinonEntropy.finite_defect_gronwall
#print axioms LatinonEntropy.total_coordinate_noise_le
