module

public import UniformLatinonLaws
public import LatinonFullDyadicKL

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical

theorem uniformLatinonLaw_real_event_le_exp {n : ℕ} (hn : 0 < n)
    (B : Set LatinonMeasure) (hB : MeasurableSet B) (A C : ℝ)
    (hnum : ((latinonEventLatinFamily hn B).card : ℝ) ≤ Real.exp A)
    (hden : Real.exp C ≤ ((allLatinSquares n).card : ℝ)) :
    (uniformLatinonLaw hn).real B ≤ Real.exp (A-C) := by
  rw [uniformLatinonLaw_real_event hn B hB]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (card_pos.mpr (allLatinSquares_nonempty n hn)))).mpr
  calc
    ((latinonEventLatinFamily hn B).card : ℝ) ≤ Real.exp A := hnum
    _ = Real.exp (A-C)*Real.exp C := by rw [← Real.exp_add,sub_add_cancel]
    _ ≤ Real.exp (A-C)*((allLatinSquares n).card : ℝ) :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

/-- Actual uniform-square probabilities satisfy the local upper bound at
each finite-rate centre,with the exact continuum rate and speed n^2. -/
theorem exists_finite_rate_uniform_latinon_local_upper (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W delta) ≤
        Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal+eps)) := by
  obtain ⟨delta,hd,NC,hNC,hcount⟩ := exists_finite_rate_latinon_local_upper W hfinite (eps/2) (half_pos heps)
  obtain ⟨ND,hND,hnorm⟩ := total_latin_square_count_normalization (eps/2) (half_pos heps)
  let N := max NC ND
  have hN : 0 < N := hNC.trans_le (le_max_left _ _)
  refine ⟨delta,hd,N,hN,?_⟩
  intro n hn
  have hnC : NC ≤ n := (le_max_left _ _).trans hn
  have hnD : ND ≤ n := (le_max_right _ _).trans hn
  have hc := hcount n hnC (latinonEventLatinFamily (hN.trans_le hn) (Metric.ball W delta))
    (fun L hL => (mem_filter.mp hL).2)
  have hp := uniformLatinonLaw_real_event_le_exp (hN.trans_le hn) (Metric.ball W delta)
    Metric.isOpen_ball.measurableSet _ _ hc (hnorm n hnD).1
  have heq : (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal+eps/2)-
      (n : ℝ)^2*(Real.log (n : ℝ)-2-eps/2) = (n : ℝ)^2*(-(latinonRate W).toReal+eps) := by ring
  rwa [heq] at hp

/-- At infinite rate,every finite exponential penalty is attained in an
actual neighborhood; infinity is never converted to a real zero. -/
theorem exists_infinite_rate_uniform_latinon_local_upper (W : LatinonMeasure)
    (htop : latinonRate W = ⊤) (T : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W delta) ≤
        Real.exp (-(n : ℝ)^2*T) := by
  obtain ⟨delta,hd,NC,hNC,hcount⟩ := exists_infinite_rate_latinon_local_upper W htop (T+1)
  obtain ⟨ND,hND,hnorm⟩ := total_latin_square_count_normalization 1 zero_lt_one
  let N := max NC ND
  have hN : 0 < N := hNC.trans_le (le_max_left _ _)
  refine ⟨delta,hd,N,hN,?_⟩
  intro n hn
  have hnC : NC ≤ n := (le_max_left _ _).trans hn
  have hnD : ND ≤ n := (le_max_right _ _).trans hn
  have hc := hcount n hnC (latinonEventLatinFamily (hN.trans_le hn) (Metric.ball W delta))
    (fun L hL => (mem_filter.mp hL).2)
  have hp := uniformLatinonLaw_real_event_le_exp (hN.trans_le hn) (Metric.ball W delta)
    Metric.isOpen_ball.measurableSet _ _ hc (hnorm n hnD).1
  have heq : (n : ℝ)^2*(Real.log (n : ℝ)-2-(T+1))-
      (n : ℝ)^2*(Real.log (n : ℝ)-2-1) = -(n : ℝ)^2*T := by ring
  rwa [heq] at hp

end LatinonEntropy

#print axioms LatinonEntropy.uniformLatinonLaw_real_event_le_exp
#print axioms LatinonEntropy.exists_finite_rate_uniform_latinon_local_upper
#print axioms LatinonEntropy.exists_infinite_rate_uniform_latinon_local_upper
