module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The elementary finite-step arguments are adapted from Graphon.Approximation;
the directed simultaneous equipartition argument is local to this project.
-/
public import LatinonBridge.CommonDirectedPartition
public import KernelCutEstimates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval ENNReal

def finitePartitionStep (P : MeasurablePartition I volume) (c : Set I → Set I → ℝ)
    (p : I × I) : ℝ :=
  ∑ A ∈ P.parts, ∑ B ∈ P.parts, (A ×ˢ B).indicator (fun _ => c A B) p

theorem finitePartitionStep_measurable (P : MeasurablePartition I volume)
    (c : Set I → Set I → ℝ) : Measurable (finitePartitionStep P c) := by
  unfold finitePartitionStep
  apply Finset.measurable_sum
  intro A hA
  apply Finset.measurable_sum
  intro B hB
  exact measurable_const.indicator ((P.measurable_parts A hA).prod (P.measurable_parts B hB))

theorem finitePartitionStep_eq_at (P : MeasurablePartition I volume) (c : Set I → Set I → ℝ)
    {p : I × I} {A B : Set I} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hp : p ∈ A ×ˢ B) :
    finitePartitionStep P c p=c A B := by
  unfold finitePartitionStep
  rw [Finset.sum_eq_single_of_mem A hA,Finset.sum_eq_single_of_mem B hB]
  · exact Set.indicator_of_mem hp _
  · intro B' hB' hne
    apply Set.indicator_of_notMem
    intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint hB hB' hne.symm) hp.2 hp'.2
  · intro A' hA' hne
    apply Finset.sum_eq_zero
    intro B' _
    apply Set.indicator_of_notMem
    intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint hA hA' hne.symm) hp.1 hp'.1

theorem finitePartitionStep_bounds (P : MeasurablePartition I volume)
    (c : Set I → Set I → ℝ)
    (hc : ∀ A ∈ P.parts, ∀ B ∈ P.parts, c A B ∈ Set.Icc (0 : ℝ) 1) (p : I × I) :
    finitePartitionStep P c p ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hr : ∃ A ∈ P.parts, p.1 ∈ A
  · obtain ⟨A,hA,hx⟩ := hr
    by_cases hs : ∃ B ∈ P.parts, p.2 ∈ B
    · obtain ⟨B,hB,hy⟩ := hs
      rw [finitePartitionStep_eq_at P c hA hB ⟨hx,hy⟩]
      exact hc A hA B hB
    · have he : finitePartitionStep P c p=0 := by
        unfold finitePartitionStep
        apply Finset.sum_eq_zero
        intro A' _
        apply Finset.sum_eq_zero
        intro B hB
        exact Set.indicator_of_notMem (fun hp => hs ⟨B,hB,hp.2⟩) _
      rw [he]
      exact ⟨le_rfl,zero_le_one⟩
  · have he : finitePartitionStep P c p=0 := by
      unfold finitePartitionStep
      apply Finset.sum_eq_zero
      intro A hA
      apply Finset.sum_eq_zero
      intro B _
      exact Set.indicator_of_notMem (fun hp => hr ⟨A,hA,hp.1⟩) _
    rw [he]
    exact ⟨le_rfl,zero_le_one⟩

/-- A whole directed step family can be re-rounded onto ONE equal-measure
partition. The exceptional-strip error is uniform in the family member. -/
theorem exists_step_family_equipartition {k q : ℕ} (hq : 0 < q)
    (P : MeasurablePartition I volume) (a : Fin k → Set I → Set I → ℝ)
    (h : Fin k → I × I → ℝ) (hh : ∀ j, Measurable (h j))
    (ha : ∀ j A B, a j A B ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ j p, h j p ∈ Set.Icc (0 : ℝ) 1)
    (hconst : ∀ j, ∀ A ∈ P.parts, ∀ B ∈ P.parts, ∀ x ∈ A, ∀ y ∈ B, h j (x,y)=a j A B) :
    ∃ Q : MeasurablePartition I volume,
    ∃ c : Fin k → Set I → Set I → ℝ,
      Q.parts.card=q ∧ (∀ A ∈ Q.parts, volume A=(1 : ℝ≥0∞)/q) ∧
      (∀ j A B, c j A B ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ j, KernelCutClose (h j) (finitePartitionStep Q (c j)) (2*(P.parts.card : ℝ)/(q : ℝ)) := by
  obtain ⟨Q,hcard,hmu,bad,hbad,hbad_le,hrefine⟩ := Graphon.exists_equipartition_almost_refining P hq
  choose par hpar_mem hpar_sub using hrefine
  let parent : Set I → Set I := fun A => if hA : A ∈ Q.parts then par A hA else ∅
  have hparent_mem (A : Set I) (hA : A ∈ Q.parts) : parent A ∈ P.parts := by
    simpa only [parent,dite_eq_left hA] using hpar_mem A hA
  have hparent_sub (A : Set I) (hA : A ∈ Q.parts) : A \ bad ⊆ parent A := by
    simpa only [parent,dite_eq_left hA] using hpar_sub A hA
  let c : Fin k → Set I → Set I → ℝ := fun j A B => a j (parent A) (parent B)
  have hcb (j : Fin k) (A B : Set I) : c j A B ∈ Set.Icc (0 : ℝ) 1 := ha j _ _
  have hbadR : (volume : Measure I).real bad ≤ (P.parts.card : ℝ)/(q : ℝ) := by
    have hqE : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
    have htop : ((P.parts.card : ℝ≥0∞)/(q : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hqE
    simpa only [measureReal_def,ENNReal.toReal_div,ENNReal.toReal_natCast] using
      ENNReal.toReal_mono htop hbad_le
  refine ⟨Q,c,hcard,hmu,hcb,?_⟩
  intro j
  have hhi : Integrable (h j) unitSquareVolume :=
    Integrable.of_mem_Icc 0 1 (hh j).aemeasurable (ae_of_all _ (hb j))
  have hvi : Integrable (finitePartitionStep Q (c j)) unitSquareVolume :=
    Integrable.of_mem_Icc 0 1 (finitePartitionStep_measurable Q (c j)).aemeasurable
      (ae_of_all _ (finitePartitionStep_bounds Q (c j) (fun A _ B _ => hcb j A B)))
  have hfst : MeasurePreserving (Prod.fst : I × I → I) unitSquareVolume volume := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : I × I → I) unitSquareVolume volume := measurePreserving_snd
  have heq : ∀ᵐ p ∂unitSquareVolume, p.1 ∉ bad → p.2 ∉ bad →
      h j p=finitePartitionStep Q (c j) p := by
    filter_upwards [hfst.quasiMeasurePreserving.ae Q.ae_covers,
      hsnd.quasiMeasurePreserving.ae Q.ae_covers] with p hp hq
    intro hxBad hyBad
    obtain ⟨A,hA,hx⟩ := hp
    obtain ⟨B,hB,hy⟩ := hq
    rw [finitePartitionStep_eq_at Q (c j) hA hB ⟨hx,hy⟩]
    exact hconst j (parent A) (hparent_mem A hA) (parent B) (hparent_mem B hB)
      p.1 (hparent_sub A hA ⟨hx,hxBad⟩) p.2 (hparent_sub B hB ⟨hy,hyBad⟩)
  apply kernelCutClose_of_L1 _ _ hhi hvi
  calc
    (∫ p, |h j p-finitePartitionStep Q (c j) p| ∂unitSquareVolume) ≤
        2*(volume : Measure I).real bad := kernel_L1_le_two_bad_strips _ _ hhi hvi
      (ae_of_all _ (hb j))
      (ae_of_all _ (finitePartitionStep_bounds Q (c j) (fun A _ B _ => hcb j A B))) bad hbad heq
    _ ≤ 2*((P.parts.card : ℝ)/(q : ℝ)) := mul_le_mul_of_nonneg_left hbadR (by norm_num)
    _ = _ := by ring

end LatinonEntropy

#print axioms LatinonEntropy.finitePartitionStep_measurable
#print axioms LatinonEntropy.finitePartitionStep_eq_at
#print axioms LatinonEntropy.finitePartitionStep_bounds
#print axioms LatinonEntropy.exists_step_family_equipartition
