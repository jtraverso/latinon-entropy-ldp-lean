module

public import LatinonBridge.LatinonGlobalDeviations
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

def latinonContractedRate {Y : Type*} (T : LatinonMeasure → Y) (z : Y) : ℝ≥0∞ :=
  ⨅ W : {W : LatinonMeasure // T W=z}, latinonRate W.1

theorem latinonContractedRate_le {Y : Type*} (T : LatinonMeasure → Y) (W : LatinonMeasure) :
    latinonContractedRate T (T W) ≤ latinonRate W :=
  iInf_le (fun V : {V : LatinonMeasure // T V=T W} => latinonRate V.1) ⟨W,rfl⟩

theorem latinonContractedRate_outside_image {Y : Type*} (T : LatinonMeasure → Y) (z : Y)
    (hz : z ∉ Set.range T) : latinonContractedRate T z=⊤ := by
  let : IsEmpty {W : LatinonMeasure // T W=z} := ⟨fun W => hz ⟨W.1,W.2⟩⟩
  simp only [latinonContractedRate,iInf_of_empty]

theorem latinonContractedRate_attained {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (T : LatinonMeasure → Y) (hT : Continuous T) (z : Y) (hz : z ∈ Set.range T) :
    ∃ W : LatinonMeasure, T W=z ∧ latinonContractedRate T z=latinonRate W := by
  have hclosed : IsClosed {W : LatinonMeasure | T W=z} := isClosed_eq hT continuous_const
  have hne : ({W : LatinonMeasure | T W=z} : Set LatinonMeasure).Nonempty := hz
  obtain ⟨W,hW,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hclosed.isCompact
    (latinon_rate_lowerSemicontinuous.lowerSemicontinuousOn _)
  refine ⟨W,hW,le_antisymm ?_ ?_⟩
  · exact iInf_le (fun V : {V : LatinonMeasure // T V=z} => latinonRate V.1) ⟨W,hW⟩
  · exact le_iInf (fun V => hmin V.2)

theorem latinonContractedRate_sublevel_image {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (T : LatinonMeasure → Y) (hT : Continuous T) (r : ℝ≥0∞) (hr : r ≠ ⊤) :
    {z | latinonContractedRate T z ≤ r}=T '' {W : LatinonMeasure | latinonRate W ≤ r} := by
  ext z
  constructor
  · intro hz
    change latinonContractedRate T z ≤ r at hz
    by_cases hin : z ∈ Set.range T
    · obtain ⟨W,hW,hRate⟩ := latinonContractedRate_attained T hT z hin
      exact ⟨W,by change latinonRate W ≤ r; rwa [← hRate],hW⟩
    · rw [latinonContractedRate_outside_image T z hin] at hz
      exact False.elim (hr (top_le_iff.mp hz))
  · rintro ⟨W,hW,rfl⟩
    exact (latinonContractedRate_le T W).trans hW

theorem latinonContractedRate_sublevels_compact {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (T : LatinonMeasure → Y) (hT : Continuous T) (r : ℝ≥0∞) (hr : r ≠ ⊤) :
    IsCompact {z | latinonContractedRate T z ≤ r} := by
  rw [latinonContractedRate_sublevel_image T hT r hr]
  exact (latinon_rate_sublevels_compact r).image hT

theorem latinonContractedRate_lowerSemicontinuous {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (T : LatinonMeasure → Y) (hT : Continuous T) : LowerSemicontinuous (latinonContractedRate T) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r=⊤
  · simp only [hr,Set.Iic_top,Set.preimage_univ,isClosed_univ]
  · exact (latinonContractedRate_sublevels_compact T hT r hr).isClosed

def latinonObservableLaw {Y : Type*} [MeasurableSpace Y]
    (T : LatinonMeasure → Y) {n : ℕ} (hn : 0 < n) : Measure Y :=
  (uniformLatinonLaw hn).map T

theorem latinonObservableLaw_real_event {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    {n : ℕ} (hn : 0 < n) (B : Set Y) (hB : MeasurableSet B) :
    (latinonObservableLaw T hn).real B=(uniformLatinonLaw hn).real (T ⁻¹' B) := by
  rw [latinonObservableLaw,measureReal_def,Measure.map_apply hT.measurable hB]
  rfl

theorem contracted_closed_uniform_latinon_upper {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    (F : Set Y) (hF : IsClosed F) (t : ℝ)
    (ht : ∀ z ∈ F, ENNReal.ofReal t ≤ latinonContractedRate T z) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (latinonObservableLaw T (hN.trans_le hn)).real F ≤ Real.exp ((n : ℝ)^2*(-t+eps)) := by
  obtain ⟨N,hN,hbound⟩ := closed_uniform_latinon_upper (T ⁻¹' F) (hF.preimage hT) t
    (fun W hW => (ht (T W) hW).trans (latinonContractedRate_le T W)) eps heps
  refine ⟨N,hN,?_⟩
  intro n hn
  rw [latinonObservableLaw_real_event T hT _ F hF.measurableSet]
  exact hbound n hn

theorem contracted_open_uniform_latinon_lower {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    (G : Set Y) (hG : IsOpen G) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∃ z ∈ G, latinonContractedRate T z ≤ ENNReal.ofReal t) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (-(n : ℝ)^2*(t+eps)) ≤ (latinonObservableLaw T (hN.trans_le hn)).real G := by
  obtain ⟨z,hz,hRate⟩ := ht
  have hin : z ∈ Set.range T := by
    by_contra hnot
    rw [latinonContractedRate_outside_image T z hnot] at hRate
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hRate)
  obtain ⟨W,hW,hI⟩ := latinonContractedRate_attained T hT z hin
  have hpre : ∃ W ∈ T ⁻¹' G, latinonRate W ≤ ENNReal.ofReal t :=
    ⟨W,by change T W ∈ G; rwa [hW],hI ▸ hRate⟩
  obtain ⟨N,hN,hbound⟩ := open_uniform_latinon_lower (T ⁻¹' G) (hG.preimage hT) t ht0 hpre eps heps
  refine ⟨N,hN,?_⟩
  intro n hn
  rw [latinonObservableLaw_real_event T hT _ G hG.measurableSet]
  exact hbound n hn

end LatinonEntropy

#print axioms LatinonEntropy.latinonContractedRate_le
#print axioms LatinonEntropy.latinonContractedRate_outside_image
#print axioms LatinonEntropy.latinonContractedRate_attained
#print axioms LatinonEntropy.latinonContractedRate_sublevel_image
#print axioms LatinonEntropy.latinonContractedRate_sublevels_compact
#print axioms LatinonEntropy.latinonContractedRate_lowerSemicontinuous
#print axioms LatinonEntropy.latinonObservableLaw_real_event
#print axioms LatinonEntropy.contracted_closed_uniform_latinon_upper
#print axioms LatinonEntropy.contracted_open_uniform_latinon_lower
