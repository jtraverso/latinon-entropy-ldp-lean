module

public import FiniteLatinLowerBound
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- A sum whose increments depend only on time reads rows chronologically. -/
theorem pathSum_eq_reverse_mapIdx_sum {Ω : Type*} (F : ℕ → Ω → ℝ) (h : List Ω) :
    pathSum (fun g a => F g.length a) h = (h.reverse.mapIdx F).sum := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih =>
    simp only [pathSum,ih,List.reverse_cons,List.mapIdx_concat,List.sum_append,
      List.sum_singleton,List.length_reverse]

theorem reverse_mapIdx_sum_eq_fin_sum {Ω : Type*} (F : ℕ → Ω → ℝ)
    (h : List Ω) (n : ℕ) (hlen : h.length = n) :
    (h.reverse.mapIdx F).sum =
      ∑ x : Fin n, F x.val (h.reverse.get ⟨x.val,by simpa only [List.length_reverse,hlen] using x.isLt⟩) := by
  have he : h.reverse.mapIdx F = List.ofFn (fun x : Fin n =>
      F x.val (h.reverse.get ⟨x.val,by simpa only [List.length_reverse,hlen] using x.isLt⟩)) := by
    apply List.ext_get
    · simp only [List.length_mapIdx,List.length_reverse,List.length_ofFn,hlen]
    · intro k hk hk'
      simp only [List.get_eq_getElem,List.getElem_mapIdx,List.getElem_ofFn]
  rw [he,List.sum_ofFn]

/-- The three-dimensional cut statistic, written directly on a Latin square. -/
def latinArrayProfileCut {n : ℕ} (P : PositiveLatinProfile n) (L : LatinArray n)
    (I U V : Finset (Fin n)) : ℝ :=
  ∑ x ∈ I, ∑ i ∈ U, ∑ j ∈ V, ((if L.val x i = j then (1 : ℝ) else 0)-P.p x i j)

def latinArrayProfileCutClose {n : ℕ} (P : PositiveLatinProfile n)
    (L : LatinArray n) (rho : ℝ) : Prop :=
  ∀ I U V : Finset (Fin n), |latinArrayProfileCut P L I U V| ≤ rho*(n : ℝ)^2

/-- The process statistic is exactly the usual tensor cut, without a change
of row order or an error term. Validity is needed only to construct the array. -/
theorem profile_cut_observation_eq_array_cut {n : ℕ} (P : PositiveLatinProfile n)
    (h : LatinHistory n) (hlen : h.length = n) (hv : LatinHistoryValid h)
    (I U V : Finset (Fin n)) :
    profileCutObservation P I U V h =
      latinArrayProfileCut P (historyToLatinArray h hlen hv) I U V := by
  let F : ℕ → Equiv.Perm (Fin n) → ℝ := fun t sigma =>
    if ht : t < n then timeCutWeight I t*
      (∑ i ∈ U, ∑ j ∈ V, (rowPermutationMatrix sigma i j-P.p ⟨t,ht⟩ i j)) else 0
  have hi : profileCutObservationIncrement P I U V = (fun g sigma => F g.length sigma) := by
    funext g sigma
    by_cases ht : g.length < n
    · simp only [profileCutObservationIncrement,profileCellObservation,F,ht,dite_true,mul_sum]
    · simp only [profileCutObservationIncrement,profileCellObservation,F,ht,dite_false,
        mul_zero,sum_const_zero]
  unfold profileCutObservation
  rw [hi,pathSum_eq_reverse_mapIdx_sum,reverse_mapIdx_sum_eq_fin_sum F h n hlen]
  simp only [F,Fin.is_lt,dite_true,timeCutWeight_at_fin]
  calc
    _ = ∑ x : Fin n, if x ∈ I then
        (∑ i ∈ U, ∑ j ∈ V, (rowPermutationMatrix
          (h.reverse.get ⟨x.val,by simpa only [List.length_reverse,hlen] using x.isLt⟩) i j-P.p x i j)) else 0 := by
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter,latinArrayProfileCut,
        historyToLatinArray,historyArray,rowPermutationMatrix]
      rfl

theorem profile_cut_close_iff_array_cut_close {n : ℕ} (P : PositiveLatinProfile n)
    (h : LatinHistory n) (hlen : h.length = n) (hv : LatinHistoryValid h) (rho : ℝ) :
    profileCutClose P h rho ↔
      latinArrayProfileCutClose P (historyToLatinArray h hlen hv) rho := by
  simp only [profileCutClose,latinArrayProfileCutClose,
    profile_cut_observation_eq_array_cut P h hlen hv]

end LatinonEntropy
