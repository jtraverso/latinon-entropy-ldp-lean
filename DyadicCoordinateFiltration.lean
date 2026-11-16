module

public import GridCoordinateIndex
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

def dyadicGridSize : ℕ → ℕ
  | 0 => 1
  | k+1 => 2*dyadicGridSize k

theorem dyadicGridSize_pos (k : ℕ) : 0 < dyadicGridSize k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (by decide) ih

theorem dyadicGridSize_eq_pow (k : ℕ) : dyadicGridSize k = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dyadicGridSize,ih,pow_succ,Nat.mul_comm]

def dyadicUnitIndex (k : ℕ) : I → Fin (dyadicGridSize k) :=
  unitGridIndex (dyadicGridSize k) (dyadicGridSize_pos k)

@[instance_reducible] def dyadicUnitSigma (k : ℕ) : MeasurableSpace I :=
  (inferInstance : MeasurableSpace (Fin (dyadicGridSize k))).comap (dyadicUnitIndex k)

theorem dyadicUnitSigma_le (k : ℕ) : dyadicUnitSigma k ≤ (inferInstance : MeasurableSpace I) :=
  (unitGridIndex_measurable (dyadicGridSize k) (dyadicGridSize_pos k)).comap_le

theorem dyadicUnitSigma_step (k : ℕ) : dyadicUnitSigma k ≤ dyadicUnitSigma (k+1) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (gridIndexParent (dyadicGridSize k))
    (measurable_of_countable _)
  exact unitGridIndex_refine (dyadicGridSize k) (dyadicGridSize_pos k)

theorem dyadicUnitSigma_monotone : Monotone dyadicUnitSigma :=
  monotone_nat_of_le_succ dyadicUnitSigma_step

def dyadicUnitFiltration : Filtration ℕ (inferInstance : MeasurableSpace I) where
  seq := dyadicUnitSigma
  mono' := dyadicUnitSigma_monotone
  le' := dyadicUnitSigma_le

theorem dyadicGridSize_inv_tendsto :
    Tendsto (fun k => 1/(dyadicGridSize k : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  simpa only [dyadicGridSize_eq_pow,Nat.cast_pow,Nat.cast_ofNat,one_div_pow] using h

def dyadicLowerApprox (k : ℕ) (u : I) : ℝ := symbolGridLower (dyadicUnitIndex k u)

theorem dyadicLowerApprox_measurable (k : ℕ) :
    Measurable[dyadicUnitSigma k] (dyadicLowerApprox k) := by
  have hf : Measurable (fun i : Fin (dyadicGridSize k) => symbolGridLower i) := measurable_of_countable _
  exact hf.comp (comap_measurable (dyadicUnitIndex k))

theorem dyadicLowerApprox_tendsto (u : I) :
    Tendsto (fun k => dyadicLowerApprox k u) atTop (𝓝 (u : ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun k => dist_nonneg) _ dyadicGridSize_inv_tendsto
  intro k
  rw [Real.dist_eq,abs_sub_comm]
  exact unitGridIndex_error (dyadicGridSize k) (dyadicGridSize_pos k) u

/-- Exact generation,including zero: no completion or null-set equality
is used to replace the Borel sigma-algebra. -/
theorem dyadicUnitSigma_iSup : (⨆ k, dyadicUnitSigma k) = (inferInstance : MeasurableSpace I) := by
  let ambient : MeasurableSpace I := inferInstance
  let sigma := ⨆ k, dyadicUnitSigma k
  have hf : ∀ k, Measurable[sigma] (dyadicLowerApprox k) := fun k =>
    (dyadicLowerApprox_measurable k).mono (le_iSup dyadicUnitSigma k) le_rfl
  have hl : Tendsto dyadicLowerApprox atTop (𝓝 (fun u : I => (u : ℝ))) :=
    tendsto_pi_nhds.mpr dyadicLowerApprox_tendsto
  have hr : Measurable[sigma] (fun u : I => (u : ℝ)) := measurable_of_tendsto_metrizable hf hl
  have hi : @Measurable I I sigma ambient id :=
    hr.subtype_mk (h := fun u => u.property)
  apply le_antisymm (iSup_le dyadicUnitSigma_le)
  simpa only [MeasurableSpace.comap_id] using hi.comap_le

end LatinonEntropy

#print axioms LatinonEntropy.dyadicGridSize_pos
#print axioms LatinonEntropy.dyadicGridSize_eq_pow
#print axioms LatinonEntropy.dyadicUnitSigma_le
#print axioms LatinonEntropy.dyadicUnitSigma_step
#print axioms LatinonEntropy.dyadicUnitSigma_monotone
#print axioms LatinonEntropy.dyadicGridSize_inv_tendsto
#print axioms LatinonEntropy.dyadicLowerApprox_measurable
#print axioms LatinonEntropy.dyadicLowerApprox_tendsto
#print axioms LatinonEntropy.dyadicUnitSigma_iSup
