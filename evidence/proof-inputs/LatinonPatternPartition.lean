module

public import LatinonPatternContinuity

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

theorem unitOrderPatternRealizations_iff_strictMono {k l : ℕ}
    (P : LatinOrderPattern k l) (z : (Fin k × Fin l) → I) :
    z ∈ unitOrderPatternRealizations P ↔ StrictMono (z ∘ P.symm) := by
  constructor
  · intro hz i j hij
    exact hz (P.symm i) (P.symm j) (by simpa only [Equiv.apply_symm_apply] using hij)
  · intro hz a b hab
    have h : (z (P.symm (P a)) : ℝ) < (z (P.symm (P b)) : ℝ) := hz hab
    simpa only [Equiv.symm_apply_apply] using h

theorem unitOrderPatternRealizations_injective {k l : ℕ} (P : LatinOrderPattern k l)
    (z : (Fin k × Fin l) → I) (hz : z ∈ unitOrderPatternRealizations P) : Injective z := by
  have hs := (unitOrderPatternRealizations_iff_strictMono P z).mp hz
  intro a b hab
  apply P.injective
  apply hs.injective
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hab

theorem unitOrderPatternRealizations_disjoint (k l : ℕ) :
    Pairwise (Disjoint on (fun P : LatinOrderPattern k l => unitOrderPatternRealizations P)) := by
  let P0 : LatinOrderPattern k l := Fintype.equivFinOfCardEq (by simp)
  intro P Q hPQ
  apply Set.disjoint_left.mpr
  intro z hzP hzQ
  let x : Fin (k*l) → I := z ∘ P0.symm
  let s : Equiv.Perm (Fin (k*l)) := P.symm.trans P0
  let t : Equiv.Perm (Fin (k*l)) := Q.symm.trans P0
  have hst : s ≠ t := by
    intro he
    have hinv : P.symm=Q.symm := Equiv.ext (fun i =>
      P0.injective (congrArg (fun e : Equiv.Perm (Fin (k*l)) => e i) he))
    apply hPQ
    simpa only [Equiv.symm_symm] using congrArg (fun e : Fin (k*l) ≃ (Fin k × Fin l) => e.symm) hinv
  have hs : x ∈ strictTupleChamber (k*l) s := by
    have hf : x ∘ s=z ∘ P.symm := by
      funext i
      exact congrArg z (P0.symm_apply_apply (P.symm i))
    change StrictMono (x ∘ s)
    rw [hf]
    exact (unitOrderPatternRealizations_iff_strictMono P z).mp hzP
  have ht : x ∈ strictTupleChamber (k*l) t := by
    have hf : x ∘ t=z ∘ Q.symm := by
      funext i
      exact congrArg z (P0.symm_apply_apply (Q.symm i))
    change StrictMono (x ∘ t)
    rw [hf]
    exact (unitOrderPatternRealizations_iff_strictMono Q z).mp hzQ
  exact Set.disjoint_left.mp (strictTupleChambers_disjoint (k*l) hst) hs ht

theorem unitOrderPatternRealizations_union (k l : ℕ) :
    (⋃ P : LatinOrderPattern k l, unitOrderPatternRealizations P)=
      {z : (Fin k × Fin l) → I | Injective z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hz
    exact unitOrderPatternRealizations_injective P z hP
  · intro hz
    let P0 : LatinOrderPattern k l := Fintype.equivFinOfCardEq (by simp)
    let x : Fin (k*l) → I := z ∘ P0.symm
    let s := Tuple.sort x
    let P : LatinOrderPattern k l := P0.trans s.symm
    refine Set.mem_iUnion.mpr ⟨P,?_⟩
    apply (unitOrderPatternRealizations_iff_strictMono P z).mpr
    change StrictMono (x ∘ s)
    exact (Tuple.monotone_sort x).strictMono_of_injective ((hz.comp P0.symm.injective).comp s.injective)

theorem unitSquareVolume_diagonal_zero : unitSquareVolume {p : I × I | p.1=p.2}=0 := by
  have hd : MeasurableSet {p : I × I | p.1=p.2} := (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [Measure.prod_apply hd]
  have hs (x : I) : (Prod.mk x) ⁻¹' {p : I × I | p.1=p.2}={x} := by
    ext y
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    exact eq_comm
  simp_rw [hs,measure_singleton]
  simp

theorem latinonPatternSampleLaw_ae_symbol_injective (W : LatinonMeasure) (k l : ℕ) :
    ∀ᵐ p ∂latinonPatternSampleLaw W k l, Injective p.2 := by
  simp only [Injective,ae_all_iff]
  intro a b
  by_cases hab : a=b
  · exact ae_of_all _ (fun _ _ => hab)
  · have hd : MeasurableSet {p : I × I | p.1=p.2} := (isClosed_eq continuous_fst continuous_snd).measurableSet
    have hz : (latinonPatternSampleLaw W k l) {p | p.2 a=p.2 b}=0 :=
      ((latinonPatternSampleLaw_pair_preserving W a b hab).measure_preimage hd.nullMeasurableSet).trans
        unitSquareVolume_diagonal_zero
    have hne : ∀ᵐ p ∂latinonPatternSampleLaw W k l, p.2 a ≠ p.2 b := by
      simpa only [ae_iff,Set.compl_ofPred,not_not] using hz
    filter_upwards [hne] with p hp he
    exact False.elim (hp he)

/-- Strict patterns exhaust the sampling law, even for singular Latinons. -/
theorem sum_latinonPatternDensity (W : LatinonMeasure) (k l : ℕ) :
    (∑ P : LatinOrderPattern k l, latinonPatternDensity W P)=1 := by
  let μ := latinonPatternSampleLaw W k l
  have hdisj : Pairwise (Disjoint on (fun P : LatinOrderPattern k l => latinonPatternEvent W P)) := by
    intro P Q hPQ
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (unitOrderPatternRealizations_disjoint k l hPQ) hp.2 hq.2
  have hae : (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P)=ᵐ[μ]
      (orderedLatinonPatternConfigs W k l ×ˢ Set.univ) := by
    filter_upwards [latinonPatternSampleLaw_ae_symbol_injective W k l] with p hp
    apply propext
    constructor
    · intro h
      obtain ⟨P,hP⟩ := Set.mem_iUnion.mp h
      exact ⟨hP.1,Set.mem_univ _⟩
    · intro h
      have hu : p.2 ∈ ⋃ P : LatinOrderPattern k l, unitOrderPatternRealizations P := by
        rw [unitOrderPatternRealizations_union]
        exact hp
      obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨P,h.1,hP⟩
  have hmass : μ.real (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P)=
      μ.real (orderedLatinonPatternConfigs W k l ×ˢ Set.univ) :=
    congrArg ENNReal.toReal (measure_congr hae)
  have hadd := measureReal_iUnion_fintype (μ := μ) hdisj (fun P => measurableSet_latinonPatternEvent W P)
  calc
    _ = ((k.factorial*l.factorial : ℕ) : ℝ)*∑ P : LatinOrderPattern k l, μ.real (latinonPatternEvent W P) := by
      unfold latinonPatternDensity
      rw [Finset.mul_sum]
    _ = ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P) :=
      congrArg (fun x : ℝ => ((k.factorial*l.factorial : ℕ) : ℝ)*x) hadd.symm
    _ = 1 := by
      rw [hmass,latinonPatternSampleLaw_ordered_univ W k l,orderedLatinonPatternConfigs_normalization W k l]

end LatinonEntropy

#print axioms LatinonEntropy.unitOrderPatternRealizations_iff_strictMono
#print axioms LatinonEntropy.unitOrderPatternRealizations_injective
#print axioms LatinonEntropy.unitOrderPatternRealizations_disjoint
#print axioms LatinonEntropy.unitOrderPatternRealizations_union
#print axioms LatinonEntropy.unitSquareVolume_diagonal_zero
#print axioms LatinonEntropy.latinonPatternSampleLaw_ae_symbol_injective
#print axioms LatinonEntropy.sum_latinonPatternDensity
