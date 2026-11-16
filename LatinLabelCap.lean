module

public import PermanentCapScalar
public import PermanentAsymptotics

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

/-- Two blocking cells give the second-order constant -2, using only the
finite scalar bound already available for a single blocking cell. -/
theorem finite_label_quadratic_cap_sum (M : ℕ) (hM : 0 < M) (s : ℝ)
    (hs : 0 ≤ s) (hcap : s ≤ (1/(M : ℝ))^2) :
    (M : ℝ)*finiteMean (fun t : Fin M => Real.log (s+(((M : ℝ)-t)/M)^2)) ≤
      -2*(M : ℝ)+2*permanentCapError 1 M := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hp : ∀ t : Fin M, 0 < ((M : ℝ)-t)/M := by
    intro t
    exact div_pos (sub_pos.mpr (Nat.cast_lt.mpr t.isLt)) hMR
  have hpoint : ∀ t : Fin M,
      Real.log (s+(((M : ℝ)-t)/M)^2) ≤
        2*Real.log (1/(M : ℝ)+((M : ℝ)-t)/M) := by
    intro t
    have hc : 0 ≤ (1/(M : ℝ))*(((M : ℝ)-t)/M) :=
      mul_nonneg (one_div_pos.mpr hMR).le (hp t).le
    have hle : s+(((M : ℝ)-t)/M)^2 ≤ (1/(M : ℝ)+((M : ℝ)-t)/M)^2 := by
      nlinarith only [hcap,hc]
    have hl := Real.log_le_log (add_pos_of_nonneg_of_pos hs (sq_pos_of_pos (hp t))) hle
    simpa only [Real.log_pow,Nat.cast_ofNat] using hl
  have hmean := finiteMean_mono hpoint
  rw [finiteMean_mul] at hmean
  have hscale := mul_le_mul_of_nonneg_left hmean hMR.le
  have hlinear := finite_label_cap_sum M 1 hM
  norm_num only [Nat.cast_one] at hlinear
  nlinarith only [hscale,hlinear]

theorem latin_label_cap_error_tendsto_zero :
    Tendsto (fun M : ℕ => 2*permanentCapError 1 M/(M : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_div_assoc,mul_zero] using (permanentCapError_div_tendsto_zero 1).const_mul 2

end LatinonEntropy

#print axioms LatinonEntropy.finite_label_quadratic_cap_sum
#print axioms LatinonEntropy.latin_label_cap_error_tendsto_zero
