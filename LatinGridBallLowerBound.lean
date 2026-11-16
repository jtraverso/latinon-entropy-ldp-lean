module

public import TensorCutLatinonBridge
public import LatinDensityLowerBound
public import UniformLatinProfile

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology MeasureTheory
open scoped Classical unitInterval

local instance (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

/-- The actual grid Latinon of the profile, with identity order map. -/
def profileToLatinonMeasure {n : ℕ} (P : PositiveLatinProfile n) : LatinonMeasure :=
  gridTensorToLatinonMeasure P.npos P.p
    (fun x y z => ((div_pos P.a_pos (Nat.cast_pos.mpr P.npos)).trans_le (P.bounds x y z).1).le)
    P.row_mass P.col_mass P.time_mass

/-- All labelled squares in the actual open metric ball, independently of
the row process and of the tensor-cut event. -/
def latinonBallLatinFamily {n : ℕ} (hn : 0 < n) (W : LatinonMeasure) (rho : ℝ) :
    Finset (LatinArray n) :=
  univ.filter (fun L => latinArrayToLatinonMeasure hn L ∈ Metric.ball W rho)

theorem tensor_family_subset_latinon_ball {n : ℕ} (P : PositiveLatinProfile n)
    (rho : ℝ) (hrho : 0 < rho) :
    latinTensorCutFamily P.p (rho/2) ⊆
      latinonBallLatinFamily P.npos (profileToLatinonMeasure P) rho := by
  intro L hL
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [Metric.mem_ball]
  exact (tensor_cut_implies_latinon_distance_bound P.npos P.p _ P.row_mass P.col_mass P.time_mass
    (rho/2) L hL).trans_lt (by linarith)

/-- C3 inside the full order-sensitive metric, with a single positive
order threshold before every bounded profile. The centres are the actual
grid-profile Latinons, not arbitrary continuum targets. -/
theorem finite_latin_grid_metric_ball_lower_bound (a b rho eta : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ P : PositiveLatinProfile n, P.a = a → P.b = b →
      (latinonBallLatinFamily P.npos (profileToLatinonMeasure P) rho).Nonempty ∧
      Real.exp (profileEntropy P-(2+eta)*(n : ℝ)^2) ≤
        (latinonBallLatinFamily P.npos (profileToLatinonMeasure P) rho).card := by
  have he := eventually_uniform_latin_tensor_lower_bound a b (rho/2) eta ha (by linarith) heta
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max 1 N,lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _),?_⟩
  intro n hn P hPa hPb
  obtain ⟨hne,hcard⟩ := hN n ((le_max_right _ _).trans hn) P hPa hPb
  have hsub := tensor_family_subset_latinon_ball P rho hrho
  exact ⟨hne.mono hsub,hcard.trans (Nat.cast_le.mpr (card_le_card hsub))⟩

/-- Exact density form of the same metric-ball bound. -/
theorem finite_latin_grid_metric_ball_density_lower_bound (a b rho eta : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ P : PositiveLatinProfile n, P.a = a → P.b = b →
      (latinonBallLatinFamily P.npos (profileToLatinonMeasure P) rho).Nonempty ∧
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+
        latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eta)) ≤
        (latinonBallLatinFamily P.npos (profileToLatinonMeasure P) rho).card := by
  obtain ⟨N,hN,hcount⟩ := finite_latin_grid_metric_ball_lower_bound a b rho eta ha hrho heta
  refine ⟨N,hN,?_⟩
  intro n hn P hPa hPb
  obtain ⟨hne,hcard⟩ := hcount n hn P hPa hPb
  refine ⟨hne,?_⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hp : ∀ x y z, 0 < P.p x y z := fun x y z =>
    (div_pos P.a_pos hnR).trans_le (P.bounds x y z).1
  have hrow : ∀ x y, (∑ z, (n : ℝ)*P.p x y z) = (n : ℝ) := by
    intro x y
    rw [← mul_sum,P.row_mass,mul_one]
  have he := scaled_density_entropy P.npos (fun x y z => (n : ℝ)*P.p x y z)
    (fun x y z => mul_pos hnR (hp x y z)) hrow
  simp only [mul_div_cancel_left₀ _ hnR.ne'] at he
  have hexp : (n : ℝ)^2*(Real.log (n : ℝ)-2+
      latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eta) =
      profileEntropy P-(2+eta)*(n : ℝ)^2 := by
    unfold profileEntropy
    rw [he]
    ring
  rw [hexp]
  exact hcard

example (n : ℕ) (hn : 0 < n) :
    (profileToLatinonMeasure (uniformLatinProfile n hn)).measure Set.univ = 1 := measure_univ

end LatinonEntropy

#print axioms LatinonEntropy.profileToLatinonMeasure
#print axioms LatinonEntropy.tensor_family_subset_latinon_ball
#print axioms LatinonEntropy.finite_latin_grid_metric_ball_lower_bound
#print axioms LatinonEntropy.finite_latin_grid_metric_ball_density_lower_bound
#print axioms LatinonEntropy.fractional_subset_sum_abs_le
#print axioms LatinonEntropy.fractional_tensor_cut_abs_le
#print axioms LatinonEntropy.gridTensorMeasure_real_box
#print axioms LatinonEntropy.gridTensorMeasure_xy_real
#print axioms LatinonEntropy.gridTensorMeasure_xz_real
#print axioms LatinonEntropy.gridTensorMeasure_yz_real
#print axioms LatinonEntropy.gridTensorToLatinonMeasure
#print axioms LatinonEntropy.gridSetWeight_bounds
#print axioms LatinonEntropy.gridTensorMeasure_weighted_box
#print axioms LatinonEntropy.finiteLatinMeasure_weighted_box
#print axioms LatinonEntropy.tensor_cut_implies_measurable_box_bound
#print axioms LatinonEntropy.tensor_cut_implies_latinon_distance_bound
