module

public import DyadicCoordinateFiltration

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

def coordinateGridIndex (n : ℕ) (hn : 0 < n) (p : (I × I) × I) : (Fin n × Fin n) × Fin n :=
  ((unitGridIndex n hn p.1.1,unitGridIndex n hn p.1.2),unitGridIndex n hn p.2)

theorem coordinateGridIndex_measurable (n : ℕ) (hn : 0 < n) : Measurable (coordinateGridIndex n hn) :=
  (((unitGridIndex_measurable n hn).comp (measurable_fst.comp measurable_fst)).prodMk
    ((unitGridIndex_measurable n hn).comp (measurable_snd.comp measurable_fst))).prodMk
      ((unitGridIndex_measurable n hn).comp measurable_snd)

theorem coordinateGridIndex_of_mem {n : ℕ} (hn : 0 < n) {p : (I × I) × I} {i j k : Fin n}
    (hi : p.1.1 ∈ lebesgueGridCell i) (hj : p.1.2 ∈ lebesgueGridCell j) (hk : p.2 ∈ lebesgueGridCell k) :
    coordinateGridIndex n hn p = ((i,j),k) := by
  unfold coordinateGridIndex
  rw [unitGridIndex_of_mem hn hi,unitGridIndex_of_mem hn hj,unitGridIndex_of_mem hn hk]

def coordinateGridParent (n : ℕ) (b : (Fin (2*n) × Fin (2*n)) × Fin (2*n)) : (Fin n × Fin n) × Fin n :=
  ((gridIndexParent n b.1.1,gridIndexParent n b.1.2),gridIndexParent n b.2)

theorem coordinateGridIndex_refine (n : ℕ) (hn : 0 < n) :
    coordinateGridIndex n hn = coordinateGridParent n ∘ coordinateGridIndex (2*n) (by omega) := by
  funext p
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun (unitGridIndex_refine n hn) p.1.1
    · exact congrFun (unitGridIndex_refine n hn) p.1.2
  · exact congrFun (unitGridIndex_refine n hn) p.2

def dyadicCubeIndex (k : ℕ) : (I × I) × I → (Fin (dyadicGridSize k) × Fin (dyadicGridSize k)) × Fin (dyadicGridSize k) :=
  coordinateGridIndex (dyadicGridSize k) (dyadicGridSize_pos k)

@[instance_reducible] def dyadicCubeSigma (k : ℕ) : MeasurableSpace ((I × I) × I) :=
  (inferInstance : MeasurableSpace ((Fin (dyadicGridSize k) × Fin (dyadicGridSize k)) × Fin (dyadicGridSize k))).comap
    (dyadicCubeIndex k)

theorem dyadicCubeSigma_le (k : ℕ) :
    dyadicCubeSigma k ≤ (inferInstance : MeasurableSpace ((I × I) × I)) :=
  (coordinateGridIndex_measurable (dyadicGridSize k) (dyadicGridSize_pos k)).comap_le

theorem dyadicCubeSigma_step (k : ℕ) : dyadicCubeSigma k ≤ dyadicCubeSigma (k+1) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (coordinateGridParent (dyadicGridSize k))
    (measurable_of_countable _)
  exact coordinateGridIndex_refine (dyadicGridSize k) (dyadicGridSize_pos k)

theorem dyadicCubeSigma_monotone : Monotone dyadicCubeSigma :=
  monotone_nat_of_le_succ dyadicCubeSigma_step

def dyadicCubeFiltration : Filtration ℕ (inferInstance : MeasurableSpace ((I × I) × I)) where
  seq := dyadicCubeSigma
  mono' := dyadicCubeSigma_monotone
  le' := dyadicCubeSigma_le

/-- Coordinate-wise reconstruction proves exact Borel generation even on
the coordinate-zero planes. No almost-everywhere replacement is assumed. -/
theorem dyadicCubeSigma_iSup :
    (⨆ k, dyadicCubeSigma k) = (inferInstance : MeasurableSpace ((I × I) × I)) := by
  let ambient : MeasurableSpace ((I × I) × I) := inferInstance
  let sigma := ⨆ k, dyadicCubeSigma k
  have hcoordinate (c : (I × I) × I → I)
      (project : ∀ k, ((Fin (dyadicGridSize k) × Fin (dyadicGridSize k)) × Fin (dyadicGridSize k)) → Fin (dyadicGridSize k))
      (he : ∀ k p, project k (dyadicCubeIndex k p) = dyadicUnitIndex k (c p)) :
      Measurable[sigma] c := by
    have hf : ∀ k, Measurable[sigma] (fun p => symbolGridLower (project k (dyadicCubeIndex k p))) := by
      intro k
      have hp : Measurable (fun b : (Fin (dyadicGridSize k) × Fin (dyadicGridSize k)) × Fin (dyadicGridSize k) =>
          symbolGridLower (project k b)) := measurable_of_countable _
      exact (hp.comp (comap_measurable (dyadicCubeIndex k))).mono (le_iSup dyadicCubeSigma k) le_rfl
    have hl : Tendsto (fun k p => symbolGridLower (project k (dyadicCubeIndex k p))) atTop
        (𝓝 (fun p => (c p : ℝ))) := by
      apply tendsto_pi_nhds.mpr
      intro p
      simpa only [he,dyadicLowerApprox] using dyadicLowerApprox_tendsto (c p)
    have hr : Measurable[sigma] (fun p => (c p : ℝ)) := measurable_of_tendsto_metrizable hf hl
    exact hr.subtype_mk
  have h1 : Measurable[sigma] (fun p : (I × I) × I => p.1.1) :=
    hcoordinate (fun p => p.1.1) (fun _ b => b.1.1) (fun _ _ => rfl)
  have h2 : Measurable[sigma] (fun p : (I × I) × I => p.1.2) :=
    hcoordinate (fun p => p.1.2) (fun _ b => b.1.2) (fun _ _ => rfl)
  have h3 : Measurable[sigma] (fun p : (I × I) × I => p.2) :=
    hcoordinate (fun p => p.2) (fun _ b => b.2) (fun _ _ => rfl)
  have hi : @Measurable ((I × I) × I) ((I × I) × I) sigma ambient id := (h1.prodMk h2).prodMk h3
  apply le_antisymm (iSup_le dyadicCubeSigma_le)
  simpa only [MeasurableSpace.comap_id] using hi.comap_le

end LatinonEntropy

#print axioms LatinonEntropy.coordinateGridIndex_measurable
#print axioms LatinonEntropy.coordinateGridIndex_of_mem
#print axioms LatinonEntropy.coordinateGridIndex_refine
#print axioms LatinonEntropy.dyadicCubeSigma_le
#print axioms LatinonEntropy.dyadicCubeSigma_step
#print axioms LatinonEntropy.dyadicCubeSigma_monotone
#print axioms LatinonEntropy.dyadicCubeSigma_iSup
