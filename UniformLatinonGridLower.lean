module

public import UniformLatinonLaws

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical

theorem uniformLatinonLaw_real_event_ge_exp {n : ℕ} (hn : 0 < n)
    (B : Set LatinonMeasure) (hB : MeasurableSet B) (A C : ℝ)
    (hnum : Real.exp A ≤ ((latinonEventLatinFamily hn B).card : ℝ))
    (hden : ((allLatinSquares n).card : ℝ) ≤ Real.exp C) :
    Real.exp (A-C) ≤ (uniformLatinonLaw hn).real B := by
  rw [uniformLatinonLaw_real_event hn B hB]
  apply (le_div_iff₀ (Nat.cast_pos.mpr (card_pos.mpr (allLatinSquares_nonempty n hn)))).mpr
  calc
    Real.exp (A-C)*((allLatinSquares n).card : ℝ) ≤ Real.exp (A-C)*Real.exp C :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = Real.exp A := by rw [← Real.exp_add,sub_add_cancel]
    _ ≤ ((latinonEventLatinFamily hn B).card : ℝ) := hnum

/-- The actual law lower bound about each grid-profile centre. Its N is
uniform before the positive profile. Approximation of a fixed continuous
centre remains a separate theorem,not an assumption of this result. -/
theorem uniform_latinon_grid_ball_lower (a b rho eps : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n)
      (P : PositiveLatinProfile n) (_hPa : P.a = a) (_hPb : P.b = b),
      Real.exp ((n : ℝ)^2*(latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eps)) ≤
        (uniformLatinonLaw (hN.trans_le hn)).real
          (Metric.ball (profileToLatinonMeasure P) rho) := by
  obtain ⟨NC,hNC,hcount⟩ := finite_latin_grid_metric_ball_density_lower_bound a b rho (eps/2)
    ha hrho (half_pos heps)
  obtain ⟨ND,hND,hnorm⟩ := total_latin_square_count_normalization (eps/2) (half_pos heps)
  let N := max NC ND
  have hN : 0 < N := hNC.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn P hPa hPb
  have hnC : NC ≤ n := (le_max_left _ _).trans hn
  have hnD : ND ≤ n := (le_max_right _ _).trans hn
  have hc := (hcount n hnC P hPa hPb).2
  have hp := uniformLatinonLaw_real_event_ge_exp (hN.trans_le hn)
    (Metric.ball (profileToLatinonMeasure P) rho) Metric.isOpen_ball.measurableSet _ _ hc (hnorm n hnD).2
  have heq : (n : ℝ)^2*(Real.log (n : ℝ)-2+
      latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eps/2)-
      (n : ℝ)^2*(Real.log (n : ℝ)-2+eps/2) =
      (n : ℝ)^2*(latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eps) := by ring
  rwa [heq] at hp

end LatinonEntropy

#print axioms LatinonEntropy.uniformLatinonLaw_real_event_ge_exp
#print axioms LatinonEntropy.uniform_latinon_grid_ball_lower
