module

public import ProfileMonitorTests

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileCutObservationIncrement {n : ℕ} (P : PositiveLatinProfile n)
    (I U V : Finset (Fin n)) (g : LatinHistory n) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, timeCutWeight I g.length*profileCellObservation P g sigma i j

def profileCutObservation {n : ℕ} (P : PositiveLatinProfile n)
    (I U V : Finset (Fin n)) (h : LatinHistory n) : ℝ :=
  pathSum (profileCutObservationIncrement P I U V) h

theorem abs_rectangle_sum_le_total {n : ℕ} (F : Fin n → Fin n → ℝ) (U V : Finset (Fin n)) :
    |∑ i ∈ U, ∑ j ∈ V, F i j| ≤ ∑ i, ∑ j, |F i j| := by
  calc
    _ ≤ ∑ i ∈ U, |∑ j ∈ V, F i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ U, ∑ j ∈ V, |F i j| := sum_le_sum (fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ U, ∑ j, |F i j| := sum_le_sum (fun i _ => sum_subset_le_total _ (fun j => abs_nonneg _) V)
    _ ≤ _ := sum_subset_le_total _ (fun i => sum_nonneg (fun j _ => abs_nonneg _)) U

theorem profile_cut_observation_increment_bound {n : ℕ} (P : PositiveLatinProfile n)
    (I U V : Finset (Fin n)) (g : LatinHistory n) (sigma : Equiv.Perm (Fin n)) :
    |profileCutObservationIncrement P I U V g sigma| ≤ 2*(n : ℝ) := by
  by_cases ht : g.length < n
  · have hA : ∀ i j, 0 ≤ rowPermutationMatrix sigma i j := by
      intro i j; unfold rowPermutationMatrix; split_ifs <;> norm_num
    have hrow : ∀ i, (∑ j, rowPermutationMatrix sigma i j) = 1 := by intro i; simp [rowPermutationMatrix]
    calc
      _ ≤ ∑ i, ∑ j, |timeCutWeight I g.length*profileCellObservation P g sigma i j| :=
        abs_rectangle_sum_le_total _ U V
      _ ≤ ∑ i, ∑ j, |profileCellObservation P g sigma i j| := by
        apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (timeCutWeight_abs_le I g.length) (abs_nonneg _)
      _ ≤ ∑ i, ∑ j, (rowPermutationMatrix sigma i j+P.p ⟨g.length,ht⟩ i j) := by
        apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
        simp only [profileCellObservation,ht,dite_true]
        calc
          _ ≤ |rowPermutationMatrix sigma i j|+|P.p ⟨g.length,ht⟩ i j| := by
            simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (rowPermutationMatrix sigma i j) (-P.p ⟨g.length,ht⟩ i j)
          _ = _ := by rw [abs_of_nonneg (hA i j),abs_of_pos (P.entry_pos _ i j)]
      _ = _ := by simp only [sum_add_distrib,hrow,P.row_mass,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]; ring
  · simp only [profileCutObservationIncrement,profileCellObservation,ht,dite_false,mul_zero,sum_const_zero,abs_zero]
    positivity

theorem pathSum_tail_bound {Ω : Type*} (X : List Ω → Ω → ℝ) (C : ℝ)
    (hbound : ∀ g a, |X g a| ≤ C) (h : List Ω) (T : ℕ) (hT : T ≤ h.length) :
    |pathSum X h-pathSum X (historyPrefix h T)| ≤ ((h.length-T : ℕ) : ℝ)*C := by
  induction h with
  | nil => have he : T = 0 := by simpa using hT
           simp [he,pathSum,historyPrefix]
  | cons a h ih =>
    by_cases ht : T ≤ h.length
    · rw [historyPrefix_cons a h T ht]
      have he : (a::h).length-T = (h.length-T)+1 := by simp only [List.length_cons]; omega
      calc
        _ = |(pathSum X h-pathSum X (historyPrefix h T))+X h a| := by rw [pathSum]; congr 1; ring
        _ ≤ |pathSum X h-pathSum X (historyPrefix h T)|+|X h a| := abs_add_le _ _
        _ ≤ ((h.length-T : ℕ) : ℝ)*C+C := add_le_add (ih ht) (hbound h a)
        _ = _ := by rw [he,Nat.cast_add,Nat.cast_one]; ring
    · have he : T = (a::h).length := by simp only [List.length_cons] at *; omega
      rw [he,historyPrefix_self]
      simp only [sub_self,abs_zero,Nat.sub_self,Nat.cast_zero,zero_mul,le_refl]

theorem profile_cut_observation_tail_bound {n : ℕ} (P : PositiveLatinProfile n)
    (I U V : Finset (Fin n)) (h : LatinHistory n) (hlen : h.length = n) (T : ℕ) (hT : T ≤ n) :
    |profileCutObservation P I U V h-profileCutObservation P I U V (historyPrefix h T)| ≤
      2*(n : ℝ)*((n : ℝ)-T) := by
  have hb := pathSum_tail_bound (profileCutObservationIncrement P I U V) (2*(n : ℝ))
    (profile_cut_observation_increment_bound P I U V) h T (by rw [hlen]; exact hT)
  rw [hlen,Nat.cast_sub hT] at hb
  exact hb.trans_eq (mul_comm _ _)

end LatinonEntropy

#print axioms LatinonEntropy.profile_cut_observation_tail_bound
