module

public import LatinonBridge.StepFamilyEquipartition

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval ENNReal

theorem kernelCutClose_congr_right_ae (g h z : I × I → ℝ) {eps : ℝ}
    (heq : h =ᵐ[unitSquareVolume] z) (hc : KernelCutClose g h eps) : KernelCutClose g z eps := by
  intro S T hS hT
  have he : (∫ p in S ×ˢ T, (g p-h p) ∂unitSquareVolume)=
      (∫ p in S ×ˢ T, (g p-z p) ∂unitSquareVolume) := by
    apply setIntegral_congr_ae (hS.prod hT)
    filter_upwards [heq] with p hp _
    rw [hp]
  rw [← he]
  exact hc S T hS hT

/-- Equal-measure cell alignment uses ONE exact MP measurable bijection
simultaneously for every directed step kernel. -/
theorem exists_common_step_cell_alignment {k q : ℕ}
    (E Q : MeasurablePartition I volume) (hE : E.parts.card=q) (hQ : Q.parts.card=q)
    (hEmu : ∀ A ∈ E.parts, volume A=(1 : ℝ≥0∞)/q)
    (hQmu : ∀ A ∈ Q.parts, volume A=(1 : ℝ≥0∞)/q)
    (c : Fin k → Set I → Set I → ℝ) (hc : ∀ j A B, c j A B ∈ Set.Icc (0 : ℝ) 1) :
    ∃ e : LatinonRelabel, ∃ r : Fin k → Set I → Set I → ℝ,
      (∀ j A B, r j A B ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ j, (fun p : I × I => finitePartitionStep Q (c j) (e p.1,e p.2)) =ᵐ[unitSquareVolume]
        finitePartitionStep E (r j) := by
  let eqE := (E.parts.equivFinOfCardEq hE).symm
  let eqQ := (Q.parts.equivFinOfCardEq hQ).symm
  let enumE : Fin q → Set I := fun i => (eqE i).1
  let enumQ : Fin q → Set I := fun i => (eqQ i).1
  have hEnumE (i : Fin q) : enumE i ∈ E.parts := (eqE i).2
  have hEnumQ (i : Fin q) : enumQ i ∈ Q.parts := (eqQ i).2
  have hinjE : Function.Injective enumE := fun i j h => eqE.injective (Subtype.ext h)
  have hinjQ : Function.Injective enumQ := fun i j h => eqQ.injective (Subtype.ext h)
  have hmass (i : Fin q) : volume (enumE i)=volume (enumQ i) := by
    rw [hEmu _ (hEnumE i),hQmu _ (hEnumQ i)]
  obtain ⟨e,he,halign⟩ := Graphon.MeasurePreserving.exists_controlled_cell_alignment E Q
    enumE enumQ hEnumE hEnumQ hinjE hinjQ hmass
  let tau : Set I → Set I := fun A => if hA : A ∈ E.parts then enumQ (eqE.symm ⟨A,hA⟩) else ∅
  have htau (A : Set I) (hA : A ∈ E.parts) : tau A ∈ Q.parts := by
    simpa only [tau,dite_eq_left hA] using hEnumQ (eqE.symm ⟨A,hA⟩)
  have hAalign (A : Set I) (hA : A ∈ E.parts) :
      ∀ᵐ x ∂(volume : Measure I), x ∈ A → e x ∈ tau A := by
    have hi := halign (eqE.symm ⟨A,hA⟩)
    simpa only [enumE,Equiv.apply_symm_apply,tau,dite_eq_left hA] using hi
  have hall : ∀ᵐ x ∂(volume : Measure I), ∀ A : {A // A ∈ E.parts}, x ∈ A.1 → e x ∈ tau A.1 :=
    ae_all_iff.mpr (fun A => hAalign A.1 A.2)
  let r : Fin k → Set I → Set I → ℝ := fun j A B => c j (tau A) (tau B)
  refine ⟨⟨e,he⟩,r,(fun j A B => hc j _ _),?_⟩
  intro j
  have hfst : MeasurePreserving (Prod.fst : I × I → I) unitSquareVolume volume := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : I × I → I) unitSquareVolume volume := measurePreserving_snd
  filter_upwards [hfst.quasiMeasurePreserving.ae E.ae_covers,
    hsnd.quasiMeasurePreserving.ae E.ae_covers,hfst.quasiMeasurePreserving.ae hall,
    hsnd.quasiMeasurePreserving.ae hall] with p hp hq hpa hqa
  obtain ⟨A,hA,hx⟩ := hp
  obtain ⟨B,hB,hy⟩ := hq
  have hxe : e p.1 ∈ tau A := hpa ⟨A,hA⟩ hx
  have hye : e p.2 ∈ tau B := hqa ⟨B,hB⟩ hy
  change finitePartitionStep Q (c j) (e p.1,e p.2)=finitePartitionStep E (r j) p
  rw [finitePartitionStep_eq_at Q (c j) (htau A hA) (htau B hB) ⟨hxe,hye⟩,
    finitePartitionStep_eq_at E (r j) hA hB ⟨hx,hy⟩]

end LatinonEntropy

#print axioms LatinonEntropy.kernelCutClose_congr_right_ae
#print axioms LatinonEntropy.exists_common_step_cell_alignment
