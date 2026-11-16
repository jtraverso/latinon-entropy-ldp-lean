module

public import LatinonGridProfile
public import LatinGridBallLowerBound
public import LatinonRelativeEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

/-- Measure domination by the uniform cube, retaining the actual density
bounds without choosing a Radon--Nikodym representative. -/
def HasLatinonDensityBounds (W : LatinonMeasure) (a b : ℝ) : Prop :=
  ∀ E : Set LatinonPoint, MeasurableSet E →
    a*uniformLatinonMeasure.measure.real E ≤ W.measure.real E ∧
      W.measure.real E ≤ b*uniformLatinonMeasure.measure.real E

theorem latinon_density_bounds_order (W : LatinonMeasure) (a b : ℝ)
    (h : HasLatinonDensityBounds W a b) : a ≤ b := by
  have hu := h Set.univ MeasurableSet.univ
  simp only [probReal_univ,mul_one] at hu
  exact hu.1.trans hu.2

theorem bounded_latinon_grid_tensor_bounds (W : LatinonMeasure) (a b : ℝ)
    (h : HasLatinonDensityBounds W a b) {n : ℕ} (hn : 0 < n) (x y z : Fin n) :
    a/(n : ℝ) ≤ latinonGridTensor W x y z ∧ latinonGridTensor W x y z ≤ b/(n : ℝ) := by
  have hb := h ((lebesgueGridCell x ×ˢ lebesgueGridCell y) ×ˢ lebesgueGridCell z)
    (((lebesgueGridCell_measurable x).prod (lebesgueGridCell_measurable y)).prod
      (lebesgueGridCell_measurable z))
  have hv : uniformLatinonMeasure.measure.real
      ((lebesgueGridCell x ×ˢ lebesgueGridCell y) ×ˢ lebesgueGridCell z) = (1/(n : ℝ))^3 := by
    change (((volume : Measure I).prod volume).prod volume).real _ = _
    rw [measureReal_prod_prod,measureReal_prod_prod,
      lebesgueGridCell_mass hn,lebesgueGridCell_mass hn,lebesgueGridCell_mass hn]
    ring
  rw [hv] at hb
  have hscale : ∀ c : ℝ, (n : ℝ)^2*(c*(1/(n : ℝ))^3) = c/(n : ℝ) := by
    intro c
    calc
      _ = c*((n : ℝ)*(1/(n : ℝ)))^2*(1/(n : ℝ)) := by ring
      _ = _ := by
        rw [mul_div_cancel₀ 1 (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
        simp only [one_pow,mul_one,div_eq_mul_inv,one_mul]
  constructor
  · have hl := mul_le_mul_of_nonneg_left hb.1 (sq_nonneg (n : ℝ))
    rwa [hscale] at hl
  · have hu := mul_le_mul_of_nonneg_left hb.2 (sq_nonneg (n : ℝ))
    rwa [hscale] at hu

/-- The C3 input is constructed from the actual measure. Unit margins and
entry bounds are conclusions, rather than extra profile hypotheses. -/
def boundedLatinonGridProfile (W : LatinonMeasure) (a b : ℝ) (ha : 0 < a)
    (h : HasLatinonDensityBounds W a b) (n : ℕ) (hn : 0 < n) : PositiveLatinProfile n where
  npos := hn
  p := latinonGridTensor W
  a := a
  b := b
  a_pos := ha
  a_le_b := latinon_density_bounds_order W a b h
  bounds := bounded_latinon_grid_tensor_bounds W a b h hn
  row_mass := latinon_grid_tensor_row_mass W hn
  col_mass := latinon_grid_tensor_col_mass W hn
  time_mass := latinon_grid_tensor_time_mass W hn

theorem uniform_latinon_density_bounds : HasLatinonDensityBounds uniformLatinonMeasure 1 1 := by
  intro E _
  simp only [one_mul,le_refl,and_self]

/-- Actual bounded Latinons supply the grid centres of the certified C3
ball count. Convergence of these centres in the full metric is separate. -/
theorem bounded_latinon_grid_ball_lower_bound (a b rho eta : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∀ (W : LatinonMeasure) (h : HasLatinonDensityBounds W a b),
      (latinonBallLatinFamily (hN.trans_le hn)
        (profileToLatinonMeasure (boundedLatinonGridProfile W a b ha h n (hN.trans_le hn))) rho).Nonempty ∧
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+
        latinGridDensityEntropy (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z)-eta)) ≤
        (latinonBallLatinFamily (hN.trans_le hn)
          (profileToLatinonMeasure (boundedLatinonGridProfile W a b ha h n (hN.trans_le hn))) rho).card := by
  obtain ⟨N,hN,hcount⟩ := finite_latin_grid_metric_ball_density_lower_bound a b rho eta ha hrho heta
  refine ⟨N,hN,?_⟩
  intro n hn W h
  exact hcount n hn (boundedLatinonGridProfile W a b ha h n (hN.trans_le hn)) rfl rfl

end LatinonEntropy

#print axioms LatinonEntropy.latinon_density_bounds_order
#print axioms LatinonEntropy.bounded_latinon_grid_tensor_bounds
#print axioms LatinonEntropy.boundedLatinonGridProfile
#print axioms LatinonEntropy.uniform_latinon_density_bounds
#print axioms LatinonEntropy.bounded_latinon_grid_ball_lower_bound
#print axioms LatinonEntropy.latinonRate_uniform
#print axioms LatinonEntropy.latinonRate_eq_zero_iff
#print axioms LatinonEntropy.latinonEntropy_nonpos
#print axioms LatinonEntropy.latinonEntropy_uniform
#print axioms LatinonEntropy.latinonEntropy_eq_bot_iff
#print axioms LatinonEntropy.relabel_uniform_latinon_measure
#print axioms LatinonEntropy.latinon_measure_rate_relabel
#print axioms LatinonEntropy.latinon_first_coordinate_preserving
#print axioms LatinonEntropy.latinon_second_coordinate_preserving
#print axioms LatinonEntropy.latinon_third_coordinate_preserving
#print axioms LatinonEntropy.latinon_grid_sum_third
#print axioms LatinonEntropy.latinon_grid_sum_second
#print axioms LatinonEntropy.latinon_grid_sum_first
#print axioms LatinonEntropy.latinon_grid_tensor_nonneg
#print axioms LatinonEntropy.latinon_grid_tensor_row_mass
#print axioms LatinonEntropy.latinon_grid_tensor_col_mass
#print axioms LatinonEntropy.latinon_grid_tensor_time_mass
