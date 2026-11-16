module

public import LatinonBridge.StepCoefficientQuantization
public import LatinonBridge.CommonCellAlignment

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- A finite net for bounded directed kernel FAMILIES modulo ONE common
exact MP bijection. Net centres need not satisfy Latinon constraints. -/
theorem exists_common_kernel_family_net (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ net : Finset (Fin k → I × I → ℝ),
      (∀ v ∈ net, ∀ j, Measurable (v j) ∧ (∀ p, v j p ∈ Set.Icc (0 : ℝ) 1)) ∧
      ∀ g : Fin k → I × I → ℝ, (∀ j, Measurable (g j)) →
        (∀ j, ∀ᵐ p ∂unitSquareVolume, g j p ∈ Set.Icc (0 : ℝ) 1) →
        ∃ e : LatinonRelabel, ∃ v ∈ net, ∀ j,
          KernelCutClose (fun p => g j (e p.1,e p.2)) (v j) eps := by
  let eta := eps/12
  have heta : 0 < eta := by dsimp [eta]; positivity
  let H := 2^(2*k*Graphon.regularityBound eta)
  let q := Nat.ceil (6*(H : ℝ)/eps)+1
  let N := Nat.ceil (3/eps)+1
  have hq : 0 < q := by dsimp [q]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hql : 6*(H : ℝ)/eps ≤ (q : ℝ) := by
    dsimp [q]
    push_cast
    linarith only [Nat.le_ceil (6*(H : ℝ)/eps)]
  have hNl : 3/eps ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    linarith only [Nat.le_ceil (3/eps)]
  have hqb : 2*(H : ℝ)/(q : ℝ) ≤ eps/3 := by
    apply (div_le_iff₀ hqR).mpr
    have hp := (div_le_iff₀ heps).mp hql
    nlinarith only [hp]
  have hNb : 1/(N : ℝ) ≤ eps/3 := by
    apply (div_le_iff₀ hNR).mpr
    have hp := (div_le_iff₀ heps).mp hNl
    nlinarith only [hp]
  obtain ⟨E,hEcard,hEmu,_⟩ := Graphon.exists_equipartition_almost_refining
    (Graphon.trivialPartition (α := I) (μ := volume)) hq
  obtain ⟨net,hnet,hcover⟩ := exists_finite_step_family_net k hN E
  refine ⟨net,hnet,?_⟩
  intro g hg hb
  obtain ⟨P,a,h,hP,ha,hdata⟩ := exists_simultaneous_directed_regular_approximation g hg hb eta heta
  obtain ⟨Q,c,hQcard,hQmu,hc,hround⟩ := exists_step_family_equipartition hq P a h
    (fun j => (hdata j).1) ha (fun j => (hdata j).2.1) (fun j => (hdata j).2.2.1)
  obtain ⟨e,r,hr,halign⟩ := exists_common_step_cell_alignment E Q hEcard hQcard hEmu hQmu c hc
  obtain ⟨v,hv,hquant⟩ := hcover r hr
  refine ⟨e,v,hv,?_⟩
  intro j
  have hgi : Integrable (g j) unitSquareVolume := Integrable.of_mem_Icc 0 1 (hg j).aemeasurable (hb j)
  have hhi : Integrable (h j) unitSquareVolume := Integrable.of_mem_Icc 0 1
    (hdata j).1.aemeasurable (ae_of_all _ (hdata j).2.1)
  have hci : Integrable (finitePartitionStep Q (c j)) unitSquareVolume :=
    Integrable.of_mem_Icc 0 1 (finitePartitionStep_measurable _ _).aemeasurable
      (ae_of_all _ (finitePartitionStep_bounds _ _ (fun A _ B _ => hc j A B)))
  have hri : Integrable (finitePartitionStep E (r j)) unitSquareVolume :=
    Integrable.of_mem_Icc 0 1 (finitePartitionStep_measurable _ _).aemeasurable
      (ae_of_all _ (finitePartitionStep_bounds _ _ (fun A _ B _ => hr j A B)))
  have hvi : Integrable (v j) unitSquareVolume := Integrable.of_mem_Icc 0 1
    (hnet v hv j).1.aemeasurable (ae_of_all _ (hnet v hv j).2)
  have hga : Integrable (fun p : I × I => g j (e p.1,e p.2)) unitSquareVolume :=
    (e.preserves.prod e.preserves).integrable_comp_of_integrable hgi
  have hfirst : KernelCutClose (g j) (h j) (4*eta) := (hdata j).2.2.2
  have hsum := kernelCutClose_triangle (g j) (h j) (finitePartitionStep Q (c j)) hgi hhi hci
    hfirst (hround j)
  have htrans := kernelCutClose_congr_right_ae _ _ _ (halign j)
    (kernelCutClose_common_pullback _ _ hsum e)
  have hfinal := kernelCutClose_triangle _ _ _ hga hri hvi htrans (hquant j)
  have hcardR : (P.parts.card : ℝ) ≤ H := by exact_mod_cast hP
  have hroundB : 2*(P.parts.card : ℝ)/(q : ℝ) ≤ eps/3 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num)) hqR.le).trans hqb
  intro S T hS hT
  have ht := hfinal S T hS hT
  dsimp only [eta] at ht
  linarith only [ht,hroundB,hNb]

end LatinonEntropy

#print axioms LatinonEntropy.exists_common_kernel_family_net
