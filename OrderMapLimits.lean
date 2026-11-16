module

public import OrderCutL1Control
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- MP order maps remain MP under convergence in measure to a measurable map. -/
theorem unit_mp_of_tendstoInMeasure (f : ℕ → I → I) (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (g : I → I) (hg : Measurable g) (hlim : TendstoInMeasure volume f atTop g) :
    MeasurePreserving g volume volume := by
  have hlaw := (hlim.tendstoInDistribution (fun n => (hf n).measurable.aemeasurable)).tendsto
  let pi : ProbabilityMeasure I := (volume : Measure I).toProbabilityMeasure
  have hm : ∀ n, (⟨(volume : Measure I).map (f n),inferInstance⟩ : ProbabilityMeasure I)=pi := by
    intro n
    apply Subtype.ext
    exact (hf n).map_eq
  simp_rw [hm] at hlaw
  have he : (⟨(volume : Measure I).map g,inferInstance⟩ : ProbabilityMeasure I)=pi :=
    tendsto_nhds_unique (X := ProbabilityMeasure I) hlaw tendsto_const_nhds
  refine ⟨hg,?_⟩
  exact congrArg Subtype.val he

theorem unit_maps_tendstoInMeasure_of_L1 (f : ℕ → I → I) (hf : ∀ n, Measurable (f n))
    (g : I → I) (hg : Measurable g)
    (hlim : Tendsto (fun n => ∫ u : I, |(f n u : ℝ)-(g u : ℝ)|) atTop (𝓝 0)) :
    TendstoInMeasure volume f atTop g := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro eps heps
  have hbound : ∀ n, (volume : Measure I).real {u | eps ≤ dist (f n u) (g u)} ≤
      (∫ u : I, |(f n u : ℝ)-(g u : ℝ)|)/eps := by
    intro n
    have hi := ((integrable_unit_coordinate (f n) (hf n)).sub (integrable_unit_coordinate g hg)).abs
    have hm := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all volume (fun u : I => abs_nonneg ((f n u : ℝ)-(g u : ℝ)))) hi eps
    apply (le_div_iff₀ heps).mpr
    simpa only [Subtype.dist_eq,Real.dist_eq,mul_comm] using hm
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa only [zero_div] using hlim.div_const eps

theorem unit_mp_of_L1_limit (f : ℕ → I → I) (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (g : I → I) (hg : Measurable g)
    (hlim : Tendsto (fun n => ∫ u : I, |(f n u : ℝ)-(g u : ℝ)|) atTop (𝓝 0)) :
    MeasurePreserving g volume volume :=
  unit_mp_of_tendstoInMeasure f hf g hg
    (unit_maps_tendstoInMeasure_of_L1 f (fun n => (hf n).measurable) g hg hlim)

theorem orderCut_Cauchy_implies_L1_Cauchy (f : ℕ → I → I)
    (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (hC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, orderCut (f m) (f n) < eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (∫ u : I, |(f m u : ℝ)-(f n u : ℝ)|) < eps := by
  intro eps heps
  obtain ⟨N,hN⟩ := hC (eps/4) (by positivity)
  refine ⟨N,?_⟩
  intro m hm n hn
  have hb := orderCut_controls_L1 (f m) (f n) (hf m) (hf n)
  have hc := hN m hm n hn
  linarith only [hb,hc,heps]

end LatinonEntropy

#print axioms LatinonEntropy.unit_mp_of_tendstoInMeasure
#print axioms LatinonEntropy.unit_maps_tendstoInMeasure_of_L1
#print axioms LatinonEntropy.unit_mp_of_L1_limit
#print axioms LatinonEntropy.orderCut_Cauchy_implies_L1_Cauchy
