module

public import Mathlib
public import LatinonSymbolCompression

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal unitInterval

def unitTupleLaw (n : ℕ) : Measure (Fin n → I) := Measure.pi (fun _ => (volume : Measure I))

instance unitTupleLaw_probability (n : ℕ) : IsProbabilityMeasure (unitTupleLaw n) := by
  unfold unitTupleLaw
  infer_instance

def strictTupleChamber (n : ℕ) (s : Equiv.Perm (Fin n)) : Set (Fin n → I) :=
  {x | StrictMono (x ∘ s)}

theorem measurableSet_strictTupleChamber (n : ℕ) (s : Equiv.Perm (Fin n)) :
    MeasurableSet (strictTupleChamber n s) := by
  unfold strictTupleChamber
  change MeasurableSet {x : Fin n → I | ∀ a b, a < b → x (s a) < x (s b)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b =>
    MeasurableSet.iInter (fun _ => measurableSet_lt
      (measurable_pi_apply (s a) : Measurable (fun x : Fin n → I => x (s a)))
      (measurable_pi_apply (s b) : Measurable (fun x : Fin n → I => x (s b))))))

theorem unitTupleLaw_ae_injective (n : ℕ) : ∀ᵐ x ∂unitTupleLaw n, Injective x := by
  simp only [Injective,ae_all_iff]
  intro i j
  by_cases hij : i=j
  · exact ae_of_all _ (fun _ _ => hij)
  · have hi := (measurable_pi_apply i : Measurable (fun x : Fin n → I => x i))
    have hj := (measurable_pi_apply j : Measurable (fun x : Fin n → I => x j))
    have h_ind := (iIndepFun_pi (μ := fun _ : Fin n => (volume : Measure I))
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
    have hmap := h_ind.map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin n => (volume : Measure I)) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n => (volume : Measure I)) j).map_eq] at hmap
    have hdiag : MeasurableSet {p : I × I | p.1=p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    have hzero : unitSquareVolume {p : I × I | p.1=p.2}=0 := by
      rw [Measure.prod_apply hdiag]
      have hsection (x : I) : (Prod.mk x) ⁻¹' {p : I × I | p.1=p.2}={x} := by
        ext y
        simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_singleton_iff]
        exact eq_comm
      simp_rw [hsection,measure_singleton]
      simp
    have hpairzero : unitTupleLaw n {x | x i=x j}=0 := by
      change (Measure.pi (fun _ : Fin n => (volume : Measure I)))
        ((fun x : Fin n → I => (x i,x j)) ⁻¹' {p : I × I | p.1=p.2})=0
      rw [← Measure.map_apply (hi.prodMk hj) hdiag,hmap]
      exact hzero
    have hne : ∀ᵐ x ∂unitTupleLaw n, x i ≠ x j := by
      simpa only [ae_iff,Set.compl_ofPred,not_not] using hpairzero
    filter_upwards [hne] with x hx heq
    exact False.elim (hx heq)

theorem strictTupleChambers_disjoint (n : ℕ) : Pairwise (Disjoint on strictTupleChamber n) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  change StrictMono (x ∘ s) at hs
  change StrictMono (x ∘ t) at ht
  have hinj : Injective x := by
    intro a b hab
    have h : s.symm a=s.symm b := hs.injective (by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hab)
    exact s.symm.injective h
  have heq := Tuple.unique_monotone hs.monotone ht.monotone
  have hst' : s=t := Equiv.ext (fun i => hinj (congrFun heq i))
  exact hst hst'

theorem strictTupleChambers_union (n : ℕ) :
    (⋃ s : Equiv.Perm (Fin n), strictTupleChamber n s)={x : Fin n → I | Injective x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hx
    change StrictMono (x ∘ s) at hs
    intro a b hab
    have h : s.symm a=s.symm b := hs.injective (by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hab)
    exact s.symm.injective h
  · intro hx
    exact Set.mem_iUnion.mpr ⟨Tuple.sort x,
      (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)⟩

theorem strictTupleChamber_mass_eq (n : ℕ) (s : Equiv.Perm (Fin n)) :
    (unitTupleLaw n).real (strictTupleChamber n s)=
      (unitTupleLaw n).real {x : Fin n → I | StrictMono x} := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => I) s.symm
  have hm : MeasurePreserving e (unitTupleLaw n) (unitTupleLaw n) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure I)) s.symm
  have heval (x : Fin n → I) (i : Fin n) : e x i=x (s i) := by
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => I) s.symm x (s i))
  have hset : e ⁻¹' {x : Fin n → I | StrictMono x}=strictTupleChamber n s := by
    ext x
    change StrictMono (e x) ↔ StrictMono (x ∘ s)
    have he : e x=x ∘ s := funext (heval x)
    rw [he]
  have hmeas : MeasurableSet {x : Fin n → I | StrictMono x} := by
    simpa only [strictTupleChamber,Equiv.coe_refl,Function.comp_id] using
      measurableSet_strictTupleChamber n (Equiv.refl _)
  have h := congrArg (fun m : Measure (Fin n → I) => m {x | StrictMono x}) hm.map_eq
  rw [Measure.map_apply hm.measurable hmeas,hset] at h
  exact congrArg ENNReal.toReal h

/-- The exact factorial normalization of strict ordering for i.i.d. uniforms. -/
theorem unitTupleLaw_strictMono_normalization (n : ℕ) :
    (n.factorial : ℝ)*(unitTupleLaw n).real {x : Fin n → I | StrictMono x}=1 := by
  have hmeas : MeasurableSet (⋃ s : Equiv.Perm (Fin n), strictTupleChamber n s) :=
    MeasurableSet.iUnion (measurableSet_strictTupleChamber n)
  have hae : ∀ᵐ x ∂unitTupleLaw n, x ∈ ⋃ s : Equiv.Perm (Fin n), strictTupleChamber n s := by
    simpa only [strictTupleChambers_union,Set.mem_ofPred_eq] using unitTupleLaw_ae_injective n
  have hmass : unitTupleLaw n (⋃ s : Equiv.Perm (Fin n), strictTupleChamber n s)=1 :=
    (mem_ae_iff_prob_eq_one hmeas).mp hae
  have hsum := measureReal_iUnion_fintype (μ := unitTupleLaw n)
    (strictTupleChambers_disjoint n) (measurableSet_strictTupleChamber n)
    (fun _ => measure_ne_top _ _)
  rw [measureReal_def,hmass,ENNReal.toReal_one] at hsum
  simp_rw [strictTupleChamber_mass_eq] at hsum
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_perm,Fintype.card_fin] using hsum.symm

theorem unitTupleLaw_order_preserving_normalization (n : ℕ) (f : I → I)
    (hf : MeasurePreserving f volume volume) :
    (n.factorial : ℝ)*(unitTupleLaw n).real {x : Fin n → I | StrictMono (f ∘ x)}=1 := by
  have hm := measurePreserving_pi (fun _ : Fin n => (volume : Measure I))
    (fun _ : Fin n => (volume : Measure I)) (fun _ => hf)
  have hmeas : MeasurableSet {x : Fin n → I | StrictMono x} := by
    simpa only [strictTupleChamber,Equiv.coe_refl,Function.comp_id] using
      measurableSet_strictTupleChamber n (Equiv.refl _)
  have h := congrArg (fun m : Measure (Fin n → I) => m {x | StrictMono x}) hm.map_eq
  rw [Measure.map_apply hm.measurable hmeas] at h
  have he : (unitTupleLaw n).real {x | StrictMono (f ∘ x)}=
      (unitTupleLaw n).real {x | StrictMono x} := congrArg ENNReal.toReal h
  rw [he]
  exact unitTupleLaw_strictMono_normalization n

end LatinonEntropy

#print axioms LatinonEntropy.unitTupleLaw_probability
#print axioms LatinonEntropy.measurableSet_strictTupleChamber
#print axioms LatinonEntropy.unitTupleLaw_ae_injective
#print axioms LatinonEntropy.strictTupleChambers_disjoint
#print axioms LatinonEntropy.strictTupleChambers_union
#print axioms LatinonEntropy.strictTupleChamber_mass_eq
#print axioms LatinonEntropy.unitTupleLaw_strictMono_normalization
#print axioms LatinonEntropy.unitTupleLaw_order_preserving_normalization
