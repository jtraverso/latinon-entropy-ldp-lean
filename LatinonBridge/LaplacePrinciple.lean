module

public import LatinonBridge.LaplaceBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical ENNReal

def latinonVariationalValues (phi : LatinonMeasure → ℝ) : Set ℝ :=
  {a | ∃ W, latinonRate W ≠ ⊤ ∧ a=phi W-(latinonRate W).toReal}

def latinonPressure (phi : LatinonMeasure → ℝ) : ℝ := sSup (latinonVariationalValues phi)

theorem latinonVariationalValues_nonempty (phi : LatinonMeasure → ℝ) :
    (latinonVariationalValues phi).Nonempty := by
  refine ⟨phi uniformLatinonMeasure,uniformLatinonMeasure,?_,?_⟩
  · rw [latinonRate_uniform]
    exact ENNReal.zero_ne_top
  · simp only [latinonRate_uniform,ENNReal.toReal_zero,sub_zero]

theorem latinonVariationalValues_bddAbove (phi : LatinonMeasure → ℝ) (hphi : Continuous phi) :
    BddAbove (latinonVariationalValues phi) := by
  obtain ⟨B,hB⟩ := exists_latinon_continuous_upper phi hphi
  refine ⟨B,?_⟩
  rintro a ⟨W,_,rfl⟩
  exact (sub_le_self _ ENNReal.toReal_nonneg).trans (hB W)

theorem finite_rate_objective_le_pressure (phi : LatinonMeasure → ℝ) (hphi : Continuous phi)
    (W : LatinonMeasure) (hW : latinonRate W ≠ ⊤) :
    phi W-(latinonRate W).toReal ≤ latinonPressure phi :=
  le_csSup (latinonVariationalValues_bddAbove phi hphi) ⟨W,hW,rfl⟩

theorem exists_finite_rate_near_pressure (phi : LatinonMeasure → ℝ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ W, latinonRate W ≠ ⊤ ∧ latinonPressure phi-eps < phi W-(latinonRate W).toReal := by
  by_contra hnot
  have hbound : ∀ W, latinonRate W ≠ ⊤ → phi W-(latinonRate W).toReal ≤ latinonPressure phi-eps := by
    intro W hW
    exact le_of_not_gt (fun h => hnot ⟨W,hW,h⟩)
  have hs : latinonPressure phi ≤ latinonPressure phi-eps :=
    csSup_le (latinonVariationalValues_nonempty phi) (by rintro a ⟨W,hW,rfl⟩; exact hbound W hW)
  linarith only [hs,heps]

/-- Two-sided exponential form of Varadhan's principle for every continuous
observable,with the true finite-rate variational supremum. -/
theorem latinon_laplace_exponential_bounds (phi : LatinonMeasure → ℝ) (hphi : Continuous phi)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(latinonPressure phi-eps)) ≤ latinonLaplace phi (hN.trans_le hn) ∧
      latinonLaplace phi (hN.trans_le hn) ≤ Real.exp ((n : ℝ)^2*(latinonPressure phi+eps)) := by
  obtain ⟨W,hW,hnear⟩ := exists_finite_rate_near_pressure phi (eps/2) (half_pos heps)
  obtain ⟨A,hA,hlo⟩ := latinon_laplace_lower_at_point phi hphi W hW (eps/2) (half_pos heps)
  obtain ⟨B,hB,hhi⟩ := latinon_laplace_upper_of_variational_bound phi hphi (latinonPressure phi)
    (finite_rate_objective_le_pressure phi hphi) eps heps
  refine ⟨max A B,hA.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnA : A ≤ n := (le_max_left _ _).trans hn
  have hnB : B ≤ n := (le_max_right _ _).trans hn
  refine ⟨?_,hhi n hnB⟩
  apply le_trans _ (hlo n hnA)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith only [hnear]

def latinonFreeEnergy (phi : LatinonMeasure → ℝ) (n : ℕ) : ℝ :=
  if hn : 0 < n then Real.log (latinonLaplace phi hn)/(n : ℝ)^2 else 0

/-- The free energy of the actual uniform Latin-square laws converges to
sup_{I(W)<infinity}(phi(W)-I(W)),at speed n^2. -/
theorem latinon_laplace_principle (phi : LatinonMeasure → ℝ) (hphi : Continuous phi) :
    Tendsto (latinonFreeEnergy phi) atTop (𝓝 (latinonPressure phi)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N,hN,hbound⟩ := latinon_laplace_exponential_bounds phi hphi (eps/2) (half_pos heps)
  refine ⟨N,?_⟩
  intro n hn
  have hnpos : 0 < n := hN.trans_le hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hnpos)
  have hb := hbound n hn
  have hZ : 0 < latinonLaplace phi hnpos := (Real.exp_pos _).trans_le hb.1
  have hloglo := Real.log_le_log (Real.exp_pos _) hb.1
  have hloghi := Real.log_le_log hZ hb.2
  rw [Real.log_exp] at hloglo hloghi
  have hlo : latinonPressure phi-eps/2 ≤ Real.log (latinonLaplace phi hnpos)/(n : ℝ)^2 := by
    apply (le_div_iff₀ hn2).mpr
    nlinarith only [hloglo]
  have hhi : Real.log (latinonLaplace phi hnpos)/(n : ℝ)^2 ≤ latinonPressure phi+eps/2 := by
    apply (div_le_iff₀ hn2).mpr
    nlinarith only [hloghi]
  rw [latinonFreeEnergy,dite_eq_left hnpos,Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith only [hlo,hhi,heps]

end LatinonEntropy

#print axioms LatinonEntropy.latinonVariationalValues_nonempty
#print axioms LatinonEntropy.latinonVariationalValues_bddAbove
#print axioms LatinonEntropy.finite_rate_objective_le_pressure
#print axioms LatinonEntropy.exists_finite_rate_near_pressure
#print axioms LatinonEntropy.latinon_laplace_exponential_bounds
#print axioms LatinonEntropy.latinon_laplace_principle
