module

public import LatinonTensorTests
public import UnitContinuousIndicator
public import LatinonCutNorms

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval BoundedContinuousFunction

/-- Fixed uniform coordinate margins upgrade weak convergence to convergence
on every measurable product box. This does not assert uniform cut convergence. -/
theorem weak_latinon_box_convergence (W : ℕ → LatinonMeasure) (V : LatinonMeasure)
    (hw : Tendsto (fun n => latinonProbability (W n)) atTop (𝓝 (latinonProbability V)))
    (S T U : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    Tendsto (fun n => (W n).measure.real ((S ×ˢ T) ×ˢ U)) atTop
      (𝓝 (V.measure.real ((S ×ˢ T) ×ˢ U))) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨a,ha,ha01,haerr⟩ := exists_continuous_unit_indicator_L1 S hS (eps/12) (by positivity)
  obtain ⟨b,hb,hb01,hberr⟩ := exists_continuous_unit_indicator_L1 T hT (eps/12) (by positivity)
  obtain ⟨c,hc,hc01,hcerr⟩ := exists_continuous_unit_indicator_L1 U hU (eps/12) (by positivity)
  have hcont : Continuous (latinonTensorTest a b c) :=
    ((ha.comp (continuous_fst.comp continuous_fst)).mul
      (hb.comp (continuous_snd.comp continuous_fst))).mul (hc.comp continuous_snd)
  let test : LatinonPoint →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨latinonTensorTest a b c,hcont⟩
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw test
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hint (eps/2) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hW := latinon_box_tensor_error (W n) S T U hS hT hU a b c
    ha.measurable hb.measurable hc.measurable ha01 hb01 hc01
  have hV := latinon_box_tensor_error V S T U hS hT hU a b c
    ha.measurable hb.measurable hc.measurable ha01 hb01 hc01
  have hnear := hN n hn
  change |(∫ p, latinonTensorTest a b c p ∂(W n).measure)-
    (∫ p, latinonTensorTest a b c p ∂V.measure)| < eps/2 at hnear
  rw [Real.dist_eq]
  have htriangle := (abs_sub_le ((W n).measure.real ((S ×ˢ T) ×ˢ U))
    (∫ p, latinonTensorTest a b c p ∂(W n).measure) (V.measure.real ((S ×ˢ T) ×ˢ U))).trans
    (add_le_add le_rfl (abs_sub_le (∫ p, latinonTensorTest a b c p ∂(W n).measure)
      (∫ p, latinonTensorTest a b c p ∂V.measure) (V.measure.real ((S ×ˢ T) ×ˢ U))))
  rw [abs_sub_comm (∫ p, latinonTensorTest a b c p ∂V.measure)] at htriangle
  linarith only [hW,hV,hnear,haerr,hberr,hcerr,htriangle]

/-- Pointwise box limits become uniform cut limits when the sequence is
already cut-Cauchy. Weak compactness alone is not used as cut compactness. -/
theorem measureCut_limit_of_box_limits (W : ℕ → LatinonMeasure) (V : LatinonMeasure)
    (hC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      measureCut (W m).measure (W n).measure < eps)
    (hbox : ∀ B : LatinonBox,
      Tendsto (fun n => (W n).measure.real B.carrier) atTop (𝓝 (V.measure.real B.carrier))) :
    Tendsto (fun n => measureCut (W n).measure V.measure) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (measureCut_nonneg _ _))
  · intro eps heps
    obtain ⟨N,hN⟩ := hC (eps/2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply lt_of_le_of_lt _ (half_lt_self heps)
    apply cutValueSup_le
    intro B
    have hlim : Tendsto (fun m => |(W n).measure.real B.carrier-(W m).measure.real B.carrier|)
        atTop (𝓝 (|(W n).measure.real B.carrier-V.measure.real B.carrier|)) :=
      (tendsto_const_nhds.sub (hbox B)).abs
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (measureCut_test_le _ _ B).trans (hN n hn m hm).le

theorem measureCut_limit_of_weak_and_Cauchy (W : ℕ → LatinonMeasure) (V : LatinonMeasure)
    (hw : Tendsto (fun n => latinonProbability (W n)) atTop (𝓝 (latinonProbability V)))
    (hC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      measureCut (W m).measure (W n).measure < eps) :
    Tendsto (fun n => measureCut (W n).measure V.measure) atTop (𝓝 0) := by
  apply measureCut_limit_of_box_limits W V hC
  intro B
  exact weak_latinon_box_convergence W V hw B.rows B.cols B.symbols
    B.rows_measurable B.cols_measurable B.symbols_measurable

end LatinonEntropy

#print axioms LatinonEntropy.weak_latinon_box_convergence
#print axioms LatinonEntropy.measureCut_limit_of_box_limits
#print axioms LatinonEntropy.measureCut_limit_of_weak_and_Cauchy
