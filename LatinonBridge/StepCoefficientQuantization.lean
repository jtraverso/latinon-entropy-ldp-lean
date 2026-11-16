module

public import LatinonBridge.StepFamilyEquipartition
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem unit_coefficient_floor_bound {N : ℕ} (hN : 0 < N) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Nat.floor (x*N) ≤ N ∧
      (Nat.floor (x*N) : ℝ)/(N : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      |x-(Nat.floor (x*N) : ℝ)/(N : ℝ)| ≤ 1/(N : ℝ) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hle : x*(N : ℝ) ≤ N := mul_le_of_le_one_left hNR.le hx.2
  have hfN : Nat.floor (x*N) ≤ N := Nat.floor_le_of_le hle
  have hfl : (Nat.floor (x*N) : ℝ) ≤ x*N := Nat.floor_le (mul_nonneg hx.1 hNR.le)
  have hfu : x*(N : ℝ) < (Nat.floor (x*N) : ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨hfN,⟨by positivity,?_⟩,?_⟩
  · apply (div_le_one hNR).mpr
    exact_mod_cast hfN
  · apply abs_le.mpr
    constructor
    · have he : 0 ≤ x-(Nat.floor (x*N) : ℝ)/(N : ℝ) := by
        rw [sub_nonneg,div_le_iff₀ hNR]
        exact hfl
      have hp : 0 < 1/(N : ℝ) := by positivity
      linarith only [he,hp]
    · apply (sub_le_iff_le_add).mpr
      rw [show 1/(N : ℝ)+(Nat.floor (x*N) : ℝ)/(N : ℝ)=
        ((Nat.floor (x*N) : ℝ)+1)/(N : ℝ) by ring]
      exact ((le_div_iff₀ hNR).mpr hfu.le)

def finiteArrayCoefficient {k N : ℕ} (E : MeasurablePartition I volume)
    (f : Fin k → {A // A ∈ E.parts} → {A // A ∈ E.parts} → Fin (N+1))
    (j : Fin k) (A B : Set I) : ℝ :=
  if hA : A ∈ E.parts then
    if hB : B ∈ E.parts then (f j ⟨A,hA⟩ ⟨B,hB⟩ : ℝ)/(N : ℝ) else 0
  else 0

theorem finiteArrayCoefficient_bounds {k N : ℕ} (hN : 0 < N)
    (E : MeasurablePartition I volume)
    (f : Fin k → {A // A ∈ E.parts} → {A // A ∈ E.parts} → Fin (N+1))
    (j : Fin k) (A B : Set I) : finiteArrayCoefficient E f j A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold finiteArrayCoefficient
  split_ifs with hA hB
  · refine ⟨by positivity,?_⟩
    apply (div_le_one (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mpr
    exact_mod_cast (Nat.le_of_lt_succ (f j ⟨A,hA⟩ ⟨B,hB⟩).isLt)
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨le_rfl,zero_le_one⟩

/-- A fixed finite partition has a finite net for ALL directed step families.
The array coordinates are independent; no symmetry is imposed. -/
theorem exists_finite_step_family_net (k : ℕ) {N : ℕ} (hN : 0 < N)
    (E : MeasurablePartition I volume) :
    ∃ net : Finset (Fin k → I × I → ℝ),
      (∀ v ∈ net, ∀ j, Measurable (v j) ∧ (∀ p, v j p ∈ Set.Icc (0 : ℝ) 1)) ∧
      ∀ c : Fin k → Set I → Set I → ℝ, (∀ j A B, c j A B ∈ Set.Icc (0 : ℝ) 1) →
        ∃ v ∈ net, ∀ j, KernelCutClose (finitePartitionStep E (c j)) (v j) (1/(N : ℝ)) := by
  let proto := fun f : Fin k → {A // A ∈ E.parts} → {A // A ∈ E.parts} → Fin (N+1) =>
    fun j => finitePartitionStep E (finiteArrayCoefficient E f j)
  let net := Finset.univ.image proto
  refine ⟨net,?_,?_⟩
  · intro v hv j
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨finitePartitionStep_measurable _ _,
      finitePartitionStep_bounds E _ (fun A _ B _ => finiteArrayCoefficient_bounds hN E f j A B)⟩
  · intro c hc
    let f : Fin k → {A // A ∈ E.parts} → {A // A ∈ E.parts} → Fin (N+1) := fun j A B =>
      ⟨Nat.floor (c j A.1 B.1*N),Nat.lt_succ_of_le (unit_coefficient_floor_bound hN _ (hc j A.1 B.1)).1⟩
    refine ⟨proto f,Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩,?_⟩
    intro j
    have h1 : Integrable (finitePartitionStep E (c j)) unitSquareVolume :=
      Integrable.of_mem_Icc 0 1 (finitePartitionStep_measurable _ _).aemeasurable
        (ae_of_all _ (finitePartitionStep_bounds E _ (fun A _ B _ => hc j A B)))
    have h2 : Integrable (proto f j) unitSquareVolume :=
      Integrable.of_mem_Icc 0 1 (finitePartitionStep_measurable _ _).aemeasurable
        (ae_of_all _ (finitePartitionStep_bounds E _
          (fun A _ B _ => finiteArrayCoefficient_bounds hN E f j A B)))
    apply kernelCutClose_of_ae_abs_le _ _ h1 h2
    have hfst : MeasurePreserving (Prod.fst : I × I → I) unitSquareVolume volume := measurePreserving_fst
    have hsnd : MeasurePreserving (Prod.snd : I × I → I) unitSquareVolume volume := measurePreserving_snd
    filter_upwards [hfst.quasiMeasurePreserving.ae E.ae_covers,
      hsnd.quasiMeasurePreserving.ae E.ae_covers] with p hp hq
    obtain ⟨A,hA,hx⟩ := hp
    obtain ⟨B,hB,hy⟩ := hq
    change |finitePartitionStep E (c j) p-finitePartitionStep E (finiteArrayCoefficient E f j) p| ≤ _
    rw [finitePartitionStep_eq_at E (c j) hA hB ⟨hx,hy⟩,
      finitePartitionStep_eq_at E (finiteArrayCoefficient E f j) hA hB ⟨hx,hy⟩]
    simpa only [finiteArrayCoefficient,dite_eq_left hA,dite_eq_left hB,f,Fin.val_mk] using
      (unit_coefficient_floor_bound hN (c j A B) (hc j A B)).2.2

end LatinonEntropy

#print axioms LatinonEntropy.unit_coefficient_floor_bound
#print axioms LatinonEntropy.finiteArrayCoefficient_bounds
#print axioms LatinonEntropy.exists_finite_step_family_net
