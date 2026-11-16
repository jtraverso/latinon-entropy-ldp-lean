module

public import LatinonFiniteSampleSupport

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem gridIndex_pair_collision_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (f g : A → I)
    (hfg : MeasurePreserving (fun x => (f x,g x)) μ unitSquareVolume)
    (n : ℕ) (hn : 0 < n) :
    μ.real {x | unitGridIndex n hn (f x)=unitGridIndex n hn (g x)} ≤ 1/(n : ℝ) := by
  let ν := finiteGridIndexLaw n hn
  let D : Set (Fin n × Fin n) := {p | p.1=p.2}
  have hm := ((unitGridIndex_preserving n hn).prod (unitGridIndex_preserving n hn)).comp hfg
  have hmass : μ.real {x | unitGridIndex n hn (f x)=unitGridIndex n hn (g x)}=(ν.prod ν).real D :=
    hm.measureReal_preimage (Set.toFinite D).measurableSet.nullMeasurableSet
  have hD : D=⋃ i : Fin n, ({i} ×ˢ {i} : Set (Fin n × Fin n)) := by
    ext p
    simp only [D,Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_singleton_iff]
    aesop
  rw [hmass,hD]
  calc
    _ ≤ ∑ i : Fin n, (ν.prod ν).real ({i} ×ˢ {i}) := measureReal_iUnion_fintype_le _
    _ = (n : ℝ)*(1/(n : ℝ))^2 := by
      simp only [measureReal_prod_prod,ν,finiteGridIndexLaw_real_atom,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ = 1/(n : ℝ) := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

def gridIndexFamilyCollision {A J : Type*} (X : J → A → I) (n : ℕ) (hn : 0 < n) : Set A :=
  {x | ¬Function.Injective (fun j => unitGridIndex n hn (X j x))}

theorem gridIndex_family_collision_le {A J : Type*} [MeasurableSpace A] [Fintype J]
    (μ : Measure A) [IsProbabilityMeasure μ] (X : J → A → I)
    (hX : ∀ i j, i ≠ j → MeasurePreserving (fun x => (X i x,X j x)) μ unitSquareVolume)
    (n : ℕ) (hn : 0 < n) :
    μ.real (gridIndexFamilyCollision X n hn) ≤ (Fintype.card J : ℝ)^2/(n : ℝ) := by
  let E := fun a b : J => if a=b then (∅ : Set A)
    else {x | unitGridIndex n hn (X a x)=unitGridIndex n hn (X b x)}
  have he : gridIndexFamilyCollision X n hn=⋃ a, ⋃ b, E a b := by
    ext x
    simp only [gridIndexFamilyCollision,Function.Injective,not_forall,
      Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨a,b,hab,hne⟩
      exact ⟨a,b,by simpa only [E,ite_eq_right hne,Set.mem_ofPred_eq] using hab⟩
    · rintro ⟨a,b,h⟩
      by_cases hab : a=b
      · simp only [E,ite_eq_left hab,Set.mem_empty_iff_false] at h
      · exact ⟨a,b,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h,hab⟩
  have hcap (a b : J) : μ.real (E a b) ≤ 1/(n : ℝ) := by
    by_cases hab : a=b
    · simp only [E,ite_eq_left hab,measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    · simpa only [E,ite_eq_right hab] using gridIndex_pair_collision_le μ (X a) (X b) (hX a b hab) n hn
  rw [he]
  calc
    _ ≤ ∑ a : J, μ.real (⋃ b, E a b) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : J, ∑ b : J, μ.real (E a b) :=
      Finset.sum_le_sum (fun a _ => measureReal_iUnion_fintype_le (E a))
    _ ≤ ∑ _a : J, ∑ _b : J, 1/(n : ℝ) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcap a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end LatinonEntropy

#print axioms LatinonEntropy.gridIndex_pair_collision_le
#print axioms LatinonEntropy.gridIndex_family_collision_le
