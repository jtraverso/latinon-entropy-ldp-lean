module

public import ProbabilityNoiseKernel
public import LatinonGridDensityIntegrals
public import GridDistributionApproximation
public import BoundedLatinonRate
public import BoundedLatinonFixedTarget

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory
open scoped Classical unitInterval ENNReal NNReal

theorem latinon_observation_density_measurable (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    Measurable (cubeObservationDensity W.measure hn) := by
  have hq : Measurable (fun b : GridBoxIndex n =>
      (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
        (unitCubeVolume.map (coordinateGridIndex n hn))) b).toReal) := measurable_of_countable _
  exact hq.comp (coordinateGridIndex_measurable n hn)

theorem latinon_observation_density_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) (p) :
    cubeObservationDensity W.measure hn p ≤ (n : ℝ)^3 := by
  change (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
    (unitCubeVolume.map (coordinateGridIndex n hn))) (coordinateGridIndex n hn p)).toReal ≤ _
  rw [coordinate_grid_rn_real W hn]
  have hm : W.measure.real (latinonGridBox (coordinateGridIndex n hn p)) ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono
      (Set.subset_univ (latinonGridBox (coordinateGridIndex n hn p)))
      (measure_ne_top W.measure Set.univ)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (pow_nonneg (Nat.cast_nonneg n) 3)

theorem latinon_observation_density_integrable (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    Integrable (cubeObservationDensity W.measure hn) unitCubeVolume := by
  apply (integrable_const ((n : ℝ)^3)).mono'
    (latinon_observation_density_measurable W hn).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs,abs_of_nonneg (cubeObservationDensity_nonneg W.measure hn p)] using
    latinon_observation_density_le W hn p

/-- Exact density of the coarsening,including when the original measure is singular. -/
theorem grid_coarsening_eq_withDensity (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    gridTensorMeasure (latinonGridTensor W (n := n)) =
      unitCubeVolume.withDensity (fun p => ENNReal.ofReal (cubeObservationDensity W.measure hn p)) := by
  have := isFiniteMeasure_withDensity_ofReal
    (latinon_observation_density_integrable W hn).hasFiniteIntegral
  apply Measure.ext_prod₃'
  intro S T U hS hT hU
  apply (measureReal_eq_measureReal_iff).mp
  rw [grid_coarsening_real_box_eq_observation_integral W hn S T U,
    withDensity_real_apply_eq_integral
      ((latinon_observation_density_measurable W hn).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun _ _ => ENNReal.ofReal_lt_top)
      (((hS.prod hT).prod hU).nullMeasurableSet)]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (cubeObservationDensity_nonneg W.measure hn p)]

theorem grid_coarsening_kl_eq_observation (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    klDiv (gridTensorMeasure (latinonGridTensor W (n := n))) unitCubeVolume =
      klDiv (W.measure.map (coordinateGridIndex n hn))
        (unitCubeVolume.map (coordinateGridIndex n hn)) := by
  let q : GridBoxIndex n → ℝ := fun b =>
    (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
      (unitCubeVolume.map (coordinateGridIndex n hn))) b).toReal
  have he := grid_coarsening_eq_withDensity W hn
  have hac : gridTensorMeasure (latinonGridTensor W (n := n)) ≪ unitCubeVolume := by
    rw [he]
    exact withDensity_absolutelyContinuous _ _
  have hrn : ∀ᵐ p ∂unitCubeVolume,
      ((gridTensorMeasure (latinonGridTensor W (n := n))).rnDeriv unitCubeVolume p).toReal =
        cubeObservationDensity W.measure hn p := by
    rw [he]
    filter_upwards [Measure.rnDeriv_withDensity unitCubeVolume
      (latinon_observation_density_measurable W hn).ennreal_ofReal] with p hp
    rw [hp,ENNReal.toReal_ofReal (cubeObservationDensity_nonneg W.measure hn p)]
  have hacmap : W.measure.map (coordinateGridIndex n hn) ≪
      unitCubeVolume.map (coordinateGridIndex n hn) :=
    finite_measure_ac_of_positive_reference _ _ (uniform_coordinate_grid_atom_ne_zero hn)
  rw [klDiv_eq_lintegral_klFun_of_ac hac,klDiv_eq_lintegral_klFun_of_ac hacmap]
  calc
    (∫⁻ p, ENNReal.ofReal (klFun
        (((gridTensorMeasure (latinonGridTensor W (n := n))).rnDeriv unitCubeVolume p).toReal)) ∂unitCubeVolume) =
      ∫⁻ p, ENNReal.ofReal (klFun (q (coordinateGridIndex n hn p))) ∂unitCubeVolume := by
        apply lintegral_congr_ae
        filter_upwards [hrn] with p hp
        rw [hp]
        rfl
    _ = ∫⁻ b, ENNReal.ofReal (klFun (q b)) ∂(unitCubeVolume.map (coordinateGridIndex n hn)) :=
      (lintegral_map (μ := unitCubeVolume)
        (measurable_of_countable (fun b : GridBoxIndex n => ENNReal.ofReal (klFun (q b))))
        (coordinateGridIndex_measurable n hn)).symm

theorem grid_coarsening_kl_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    klDiv (gridTensorMeasure (latinonGridTensor W (n := n))) unitCubeVolume ≤ latinonRate W := by
  rw [grid_coarsening_kl_eq_observation W hn]
  exact klDiv_map_le W.measure unitCubeVolume (coordinateGridIndex_measurable n hn)

/-- Coarsen the actual measure while retaining the original order map. -/
def coarsenedLatinon (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) : LatinonMeasure :=
  { (gridTensorToLatinonMeasure hn (latinonGridTensor W)
      (latinon_grid_tensor_nonneg W) (latinon_grid_tensor_row_mass W hn)
      (latinon_grid_tensor_col_mass W hn) (latinon_grid_tensor_time_mass W hn)) with
    order := W.order
    order_preserving := W.order_preserving }

theorem coarsenedLatinon_rate_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    latinonRate (coarsenedLatinon W hn) ≤ latinonRate W :=
  grid_coarsening_kl_le W hn

theorem coarsenedLatinon_dist_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    dist W (coarsenedLatinon W hn) ≤
      measureCut W.measure (gridTensorMeasure (latinonGridTensor W (n := n))) := by
  apply (latinonCutDistance_le_cost W (coarsenedLatinon W hn)
    LatinonRelabel.refl LatinonRelabel.refl).trans
  change orderCut W.order W.order+orderCut W.order W.order+
    measureCut W.measure (relabelLatinonMeasure (coarsenedLatinon W hn).measure
      LatinonRelabel.refl LatinonRelabel.refl) ≤ _
  simp only [orderCut_self,relabelLatinonMeasure_refl,zero_add]
  exact le_rfl

theorem coarsenedLatinon_density_upper (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (E : Set LatinonPoint) (hE : MeasurableSet E) :
    (coarsenedLatinon W hn).measure.real E ≤ (n : ℝ)^3*uniformLatinonMeasure.measure.real E := by
  change (gridTensorMeasure (latinonGridTensor W (n := n))).real E ≤ _
  rw [grid_coarsening_eq_withDensity W hn,
    withDensity_real_apply_eq_integral
      ((latinon_observation_density_measurable W hn).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun _ _ => ENNReal.ofReal_lt_top) hE.nullMeasurableSet]
  have he : (∫ p in E, (ENNReal.ofReal (cubeObservationDensity W.measure hn p)).toReal ∂unitCubeVolume) =
      ∫ p in E, cubeObservationDensity W.measure hn p ∂unitCubeVolume := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [ENNReal.toReal_ofReal (cubeObservationDensity_nonneg W.measure hn p)]
  rw [he]
  have hi := integral_mono_ae (latinon_observation_density_integrable W hn).integrableOn
    (integrable_const ((n : ℝ)^3) : Integrable (fun _ : LatinonPoint => (n : ℝ)^3) (unitCubeVolume.restrict E))
    (ae_of_all _ fun p => latinon_observation_density_le W hn p)
  simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm,
    unitCubeVolume,uniformLatinonMeasure] using hi

/-- Uniform resampling preserves all pair margins and retains the actual order. -/
def uniformLatinonMixture (W : LatinonMeasure) (s t : ℝ≥0) (hst : s+t=1) : LatinonMeasure where
  measure := s • W.measure+t • uniformLatinonMeasure.measure
  order := W.order
  order_preserving := W.order_preserving
  xy_uniform := by
    intro S T hS hT
    simp only [Measure.add_apply,Measure.coe_nnreal_smul_apply,W.xy_uniform S T hS hT,
      uniformLatinonMeasure.xy_uniform S T hS hT]
    rw [← add_mul,← ENNReal.coe_add,hst,ENNReal.coe_one,one_mul]
  xz_uniform := by
    intro S U hS hU
    simp only [Measure.add_apply,Measure.coe_nnreal_smul_apply,W.xz_uniform S U hS hU,
      uniformLatinonMeasure.xz_uniform S U hS hU]
    rw [← add_mul,← ENNReal.coe_add,hst,ENNReal.coe_one,one_mul]
  yz_uniform := by
    intro T U hT hU
    simp only [Measure.add_apply,Measure.coe_nnreal_smul_apply,W.yz_uniform T U hT hU,
      uniformLatinonMeasure.yz_uniform T U hT hU]
    rw [← add_mul,← ENNReal.coe_add,hst,ENNReal.coe_one,one_mul]

theorem uniformLatinonMixture_real (W : LatinonMeasure) (s t : ℝ≥0) (hst : s+t=1) (E) :
    (uniformLatinonMixture W s t hst).measure.real E =
      (s : ℝ)*W.measure.real E+(t : ℝ)*uniformLatinonMeasure.measure.real E := by
  change (s • W.measure+t • uniformLatinonMeasure.measure).real E = _
  rw [measureReal_add_apply,measureReal_nnreal_smul_apply,measureReal_nnreal_smul_apply]

theorem uniformLatinonMixture_rate_le (W : LatinonMeasure) (s t : ℝ≥0) (hst : s+t=1) :
    latinonRate (uniformLatinonMixture W s t hst) ≤ latinonRate W := by
  change klDiv (s • W.measure+t • uniformLatinonMeasure.measure) uniformLatinonMeasure.measure ≤ _
  exact klDiv_probability_noise_le W.measure uniformLatinonMeasure.measure s t (by exact_mod_cast hst)

theorem uniformLatinonMixture_density_bounds (W : LatinonMeasure) (s t : ℝ≥0)
    (hst : s+t=1) (B : ℝ)
    (hB : ∀ E, MeasurableSet E → W.measure.real E ≤ B*uniformLatinonMeasure.measure.real E) :
    HasLatinonDensityBounds (uniformLatinonMixture W s t hst) t ((s : ℝ)*B+t) := by
  intro E hE
  rw [uniformLatinonMixture_real]
  constructor
  · exact le_add_of_nonneg_left (mul_nonneg s.coe_nonneg measureReal_nonneg)
  · have hh := mul_le_mul_of_nonneg_left (hB E hE) s.coe_nonneg
    nlinarith only [hh]

theorem uniformLatinonMixture_measureCut_le (W : LatinonMeasure) (s t : ℝ≥0) (hst : s+t=1) :
    measureCut W.measure (uniformLatinonMixture W s t hst).measure ≤ t := by
  have hsum : (s : ℝ)+(t : ℝ)=1 := by exact_mod_cast hst
  apply cutValueSup_le
  intro B
  let E := (B.rows ×ˢ B.cols) ×ˢ B.symbols
  change |W.measure.real E-(uniformLatinonMixture W s t hst).measure.real E| ≤ _
  rw [uniformLatinonMixture_real]
  have heq : W.measure.real E-((s : ℝ)*W.measure.real E+
      (t : ℝ)*uniformLatinonMeasure.measure.real E) =
        (t : ℝ)*(W.measure.real E-uniformLatinonMeasure.measure.real E) := by
    have hs : (s : ℝ)=1-(t : ℝ) := by linarith only [hsum]
    rw [hs]
    ring
  rw [heq,abs_mul,abs_of_nonneg t.coe_nonneg]
  have hb := probability_real_set_bounds W.measure E
  have hu := probability_real_set_bounds uniformLatinonMeasure.measure E
  have hd : |W.measure.real E-uniformLatinonMeasure.measure.real E| ≤ 1 :=
    abs_sub_le_one_of_unit_bounds hb hu
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd t.coe_nonneg

theorem uniformLatinonMixture_dist_le (W : LatinonMeasure) (s t : ℝ≥0) (hst : s+t=1) :
    dist W (uniformLatinonMixture W s t hst) ≤ t := by
  apply (latinonCutDistance_le_cost W (uniformLatinonMixture W s t hst)
    LatinonRelabel.refl LatinonRelabel.refl).trans
  change orderCut W.order W.order+orderCut W.order W.order+
    measureCut W.measure (relabelLatinonMeasure (uniformLatinonMixture W s t hst).measure
      LatinonRelabel.refl LatinonRelabel.refl) ≤ _
  simpa only [orderCut_self,relabelLatinonMeasure_refl,zero_add] using
    uniformLatinonMixture_measureCut_le W s t hst

/-- Every finite-rate Latinon has nearby bounded positive Latinons of no
larger rate,in the full order-sensitive metric. The approximation is constructed. -/
theorem exists_bounded_latinon_regularization (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (rho : ℝ) (hrho : 0 < rho) :
    ∃ (V : LatinonMeasure) (a b : ℝ), 0 < a ∧ HasLatinonDensityBounds V a b ∧
      dist W V < rho ∧ latinonRate V ≤ latinonRate W := by
  obtain ⟨N,hN,hcut⟩ := exists_finite_rate_grid_distribution_cut W hfinite (rho/4) (by positivity)
  let C := coarsenedLatinon W hN
  let delta : ℝ := min (1/2) (rho/4)
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdeltaHalf : delta ≤ 1/2 := min_le_left _ _
  have hdeltaRho : delta ≤ rho/4 := min_le_right _ _
  let s : ℝ≥0 := Real.toNNReal (1-delta)
  let t : ℝ≥0 := Real.toNNReal delta
  have hs : (s : ℝ)=1-delta := Real.coe_toNNReal _ (by linarith only [hdeltaHalf])
  have ht : (t : ℝ)=delta := Real.coe_toNNReal _ hdelta.le
  have hst : s+t=1 := by
    apply NNReal.coe_injective
    change (s : ℝ)+(t : ℝ)=1
    rw [hs,ht]
    ring
  let V := uniformLatinonMixture C s t hst
  refine ⟨V,t,(s : ℝ)*(N : ℝ)^3+t,?_,?_,?_,?_⟩
  · rwa [ht]
  · exact uniformLatinonMixture_density_bounds C s t hst ((N : ℝ)^3)
      (coarsenedLatinon_density_upper W hN)
  · have hc : dist W C ≤ rho/4 := (coarsenedLatinon_dist_le W hN).trans (hcut N le_rfl)
    have hm : dist C V ≤ delta := by
      simpa only [ht] using uniformLatinonMixture_dist_le C s t hst
    apply (dist_triangle W C V).trans_lt
    linarith only [hc,hm,hdeltaRho,hrho]
  · exact (uniformLatinonMixture_rate_le C s t hst).trans (coarsenedLatinon_rate_le W hN)

/-- Local lower bound at every finite-rate Latinon,with no density bounds. -/
theorem finite_rate_uniform_latinon_local_lower (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (rho eta : ℝ) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) ≤
        (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W rho) := by
  obtain ⟨V,a,b,ha,hbounds,hd,hrate⟩ :=
    exists_bounded_latinon_regularization W hfinite (rho/2) (half_pos hrho)
  obtain ⟨N,hN,hprob⟩ := bounded_uniform_latinon_local_lower V a b ha hbounds
    (rho/2) eta (half_pos hrho) heta
  have hr : (latinonRate V).toReal ≤ (latinonRate W).toReal := ENNReal.toReal_mono hfinite hrate
  refine ⟨N,hN,?_⟩
  intro n hn
  have hsubset : Metric.ball V (rho/2) ⊆ Metric.ball W rho := by
    intro X hX
    change dist X V < rho/2 at hX
    change dist X W < rho
    have hd' : dist V W < rho/2 := by simpa only [dist_comm] using hd
    exact (dist_triangle X V W).trans_lt (by linarith only [hX,hd'])
  calc
    Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) ≤
        Real.exp ((n : ℝ)^2*(-(latinonRate V).toReal-eta)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith only [hr]) (sq_nonneg (n : ℝ))
    _ ≤ (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball V (rho/2)) := hprob n hn
    _ ≤ (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W rho) :=
      measureReal_mono hsubset (measure_ne_top (uniformLatinonLaw (hN.trans_le hn)) _)

/-- Open-set lower bound for the actual uniform laws in the full topology. -/
theorem open_uniform_latinon_lower_at_point (G : Set LatinonMeasure) (hG : IsOpen G)
    (W : LatinonMeasure) (hW : W ∈ G) (hfinite : latinonRate W ≠ ⊤)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) ≤
        (uniformLatinonLaw (hN.trans_le hn)).real G := by
  obtain ⟨rho,hrho,hball⟩ := Metric.isOpen_iff.mp hG W hW
  obtain ⟨N,hN,hprob⟩ := finite_rate_uniform_latinon_local_lower W hfinite rho eta hrho heta
  refine ⟨N,hN,?_⟩
  intro n hn
  exact (hprob n hn).trans
    (measureReal_mono hball (measure_ne_top (uniformLatinonLaw (hN.trans_le hn)) _))

/-- The open lower LDP in strict-threshold form,so no infinite rate is
silently converted to zero. Its hypothesis is exactly a point below t. -/
theorem open_uniform_latinon_lower_threshold (G : Set LatinonMeasure) (hG : IsOpen G)
    (t : ℝ) (ht : ∃ W ∈ G, latinonRate W < ENNReal.ofReal t) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (-(n : ℝ)^2*t) ≤ (uniformLatinonLaw (hN.trans_le hn)).real G := by
  obtain ⟨W,hW,hrate⟩ := ht
  have hfinite : latinonRate W ≠ ⊤ := hrate.ne_top
  have hgap : 0 < t-(latinonRate W).toReal :=
    sub_pos.mpr (ENNReal.toReal_lt_of_lt_ofReal hrate)
  obtain ⟨N,hN,hprob⟩ := open_uniform_latinon_lower_at_point G hG W hW hfinite
    (t-(latinonRate W).toReal) hgap
  refine ⟨N,hN,?_⟩
  intro n hn
  have he : (n : ℝ)^2*(-(latinonRate W).toReal-(t-(latinonRate W).toReal)) = -(n : ℝ)^2*t := by ring
  simpa only [he] using hprob n hn

/-- Fixed-target entropy lower count for every finite-rate Latinon. -/
theorem finite_rate_latinon_fixed_target_count_lower (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (rho eta : ℝ) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) := by
  obtain ⟨V,a,b,ha,hbounds,hd,hrate⟩ :=
    exists_bounded_latinon_regularization W hfinite (rho/2) (half_pos hrho)
  obtain ⟨N,hN,hcount⟩ := bounded_latinon_fixed_target_count_lower V a b ha hbounds
    (rho/2) eta (half_pos hrho) heta
  have hr : (latinonRate V).toReal ≤ (latinonRate W).toReal := ENNReal.toReal_mono hfinite hrate
  refine ⟨N,hN,?_⟩
  intro n hn
  have hsub : latinonBallLatinFamily (hN.trans_le hn) V (rho/2) ⊆
      latinonBallLatinFamily (hN.trans_le hn) W rho := by
    intro L hL
    apply Finset.mem_filter.mpr
    have hm := (Finset.mem_filter.mp hL).2
    refine ⟨Finset.mem_univ _,?_⟩
    change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) V < rho/2 at hm
    change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) W < rho
    have hd' : dist V W < rho/2 := by simpa only [dist_comm] using hd
    exact (dist_triangle _ V W).trans_lt (by linarith only [hm,hd'])
  calc
    Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate V).toReal-eta)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith only [hr]) (sq_nonneg (n : ℝ))
    _ ≤ ((latinonBallLatinFamily (hN.trans_le hn) V (rho/2)).card : ℝ) := hcount n hn
    _ ≤ ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)

/-- Full local entropy counting formula for all finite-rate Latinons,
including densities without positive lower or finite upper bounds. -/
theorem finite_rate_latinon_entropy_count (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) ∧
      ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal+eta)) := by
  obtain ⟨delta,hd,NU,hNU,hupper⟩ := exists_finite_rate_latinon_local_upper W hfinite eta heta
  let rho := min delta r
  have hrho : 0 < rho := lt_min hd hr
  obtain ⟨NL,hNL,hlower⟩ := finite_rate_latinon_fixed_target_count_lower W hfinite rho eta hrho heta
  let N := max NL NU
  have hN : 0 < N := hNL.trans_le (le_max_left _ _)
  refine ⟨rho,hrho,min_le_right _ _,N,hN,?_⟩
  intro n hn
  have hnL : NL ≤ n := (le_max_left _ _).trans hn
  have hnU : NU ≤ n := (le_max_right _ _).trans hn
  refine ⟨hlower n hnL,?_⟩
  apply hupper n hnU (latinonBallLatinFamily (hN.trans_le hn) W rho)
  intro L hL
  have hm := (Finset.mem_filter.mp hL).2
  change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) W < rho at hm
  change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) W < delta
  exact hm.trans_le (min_le_left _ _)

end LatinonEntropy

#print axioms LatinonEntropy.latinon_observation_density_measurable
#print axioms LatinonEntropy.latinon_observation_density_le
#print axioms LatinonEntropy.latinon_observation_density_integrable
#print axioms LatinonEntropy.grid_coarsening_eq_withDensity
#print axioms LatinonEntropy.grid_coarsening_kl_eq_observation
#print axioms LatinonEntropy.grid_coarsening_kl_le
#print axioms LatinonEntropy.coarsenedLatinon
#print axioms LatinonEntropy.coarsenedLatinon_rate_le
#print axioms LatinonEntropy.coarsenedLatinon_dist_le
#print axioms LatinonEntropy.coarsenedLatinon_density_upper
#print axioms LatinonEntropy.uniformLatinonMixture
#print axioms LatinonEntropy.uniformLatinonMixture_real
#print axioms LatinonEntropy.uniformLatinonMixture_rate_le
#print axioms LatinonEntropy.uniformLatinonMixture_density_bounds
#print axioms LatinonEntropy.uniformLatinonMixture_measureCut_le
#print axioms LatinonEntropy.uniformLatinonMixture_dist_le
#print axioms LatinonEntropy.exists_bounded_latinon_regularization
#print axioms LatinonEntropy.finite_rate_uniform_latinon_local_lower
#print axioms LatinonEntropy.open_uniform_latinon_lower_at_point
#print axioms LatinonEntropy.open_uniform_latinon_lower_threshold
#print axioms LatinonEntropy.finite_rate_latinon_fixed_target_count_lower
#print axioms LatinonEntropy.finite_rate_latinon_entropy_count
