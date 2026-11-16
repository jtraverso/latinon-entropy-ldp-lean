module

public import OrderMapLimits
public import LatinonOrderPermutation
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

theorem dist_real_toL1_eq_integral_abs (a b : I → ℝ) (ha : Integrable a volume) (hb : Integrable b volume) :
    dist (ha.toL1 a) (hb.toL1 b) = ∫ u : I, |a u-b u| := by
  rw [dist_edist,Integrable.edist_toL1_toL1]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all volume (fun u => abs_nonneg (a u-b u)))
    (ha.sub hb).abs.aestronglyMeasurable]
  simp only [edist_dist,Real.dist_eq]

/-- Construct the actual MP L1 limit of an order-cut-Cauchy sequence.
The limit is chosen in complete L1,shown I-valued a.e.,then clipped measurably. -/
theorem exists_MP_L1_limit_of_orderCut_Cauchy (f : ℕ → I → I)
    (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (hC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, orderCut (f m) (f n) < eps) :
    ∃ g : I → I, MeasurePreserving g volume volume ∧
      Tendsto (fun n => ∫ u : I, |(f n u : ℝ)-(g u : ℝ)|) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (fun u : I => (f n u : ℝ)) volume :=
    integrable_unit_coordinate (f n) (hf n).measurable
  let F : ℕ → Lp ℝ 1 (volume : Measure I) := fun n => (hi n).toL1 (fun u => (f n u : ℝ))
  have hLC := orderCut_Cauchy_implies_L1_Cauchy f hf hC
  have hFC : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N,hN⟩ := hLC eps heps
    refine ⟨N,?_⟩
    intro m hm n hn
    change dist ((hi m).toL1 (fun u => (f m u : ℝ))) ((hi n).toL1 (fun u => (f n u : ℝ))) < eps
    rw [dist_real_toL1_eq_integral_abs]
    exact hN m hm n hn
  obtain ⟨G,hG⟩ := cauchySeq_tendsto_of_complete hFC
  have hFae (n : ℕ) : F n =ᵐ[volume] (fun u => (f n u : ℝ)) := (hi n).coeFn_toL1
  have hall : ∀ᵐ u ∂(volume : Measure I), ∀ n, F n u=(f n u : ℝ) := ae_all_iff.mpr hFae
  obtain ⟨phi,_,hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hGAE : ∀ᵐ u ∂(volume : Measure I), G u ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hseq,hall] with u hlimu hFu
    apply isClosed_Icc.mem_of_tendsto hlimu
    exact Eventually.of_forall (fun n => by rw [hFu (phi n)]; exact (f (phi n) u).property)
  let g : I → I := fun u => ⟨max 0 (min 1 (G u)),le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩
  have hgm : Measurable g :=
    (measurable_const.max (measurable_const.min (Lp.stronglyMeasurable G).measurable)).subtype_mk
  have hgeq : (fun u => (g u : ℝ)) =ᵐ[volume] G := by
    filter_upwards [hGAE] with u hu
    change max 0 (min 1 (G u))=G u
    rw [min_eq_right hu.2,max_eq_right hu.1]
  have hGL1 : (integrable_unit_coordinate g hgm).toL1 (fun u => (g u : ℝ))=G := by
    apply Lp.ext
    exact (integrable_unit_coordinate g hgm).coeFn_toL1.trans hgeq
  have hdist := (tendsto_iff_dist_tendsto_zero).mp hG
  rw [← hGL1] at hdist
  have hD : Tendsto (fun n => ∫ u : I, |(f n u : ℝ)-(g u : ℝ)|) atTop (𝓝 0) := by
    simpa only [F,dist_real_toL1_eq_integral_abs] using hdist
  exact ⟨g,unit_mp_of_L1_limit f hf g hgm hD,hD⟩

theorem orderCut_tendsto_of_L1 (f : ℕ → I → I) (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (g : I → I) (hg : Measurable g)
    (hlim : Tendsto (fun n => ∫ u : I, |(f n u : ℝ)-(g u : ℝ)|) atTop (𝓝 0)) :
    Tendsto (fun n => orderCut (f n) g) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (orderCut_nonneg (f n) g))
  · intro eps heps
    have hsmall := hlim.eventually_lt_const (show 0 < eps^2/256 by positivity)
    filter_upwards [hsmall] with n hn
    have hb := orderCut_L1_bound (f n) g (hf n) hg (eps/16) (by positivity)
    by_contra hnot
    have hscaled := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (by positivity : (0 : ℝ) ≤ eps/16)
    nlinarith only [hb,hn,hscaled,sq_pos_of_pos heps]

theorem exists_MP_orderCut_limit (f : ℕ → I → I) (hf : ∀ n, MeasurePreserving (f n) volume volume)
    (hC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, orderCut (f m) (f n) < eps) :
    ∃ g : I → I, MeasurePreserving g volume volume ∧
      Tendsto (fun n => orderCut (f n) g) atTop (𝓝 0) := by
  obtain ⟨g,hg,hL1⟩ := exists_MP_L1_limit_of_orderCut_Cauchy f hf hC
  exact ⟨g,hg,orderCut_tendsto_of_L1 f hf g hg.measurable hL1⟩

end LatinonEntropy

#print axioms LatinonEntropy.dist_real_toL1_eq_integral_abs
#print axioms LatinonEntropy.exists_MP_L1_limit_of_orderCut_Cauchy
#print axioms LatinonEntropy.orderCut_tendsto_of_L1
#print axioms LatinonEntropy.exists_MP_orderCut_limit
