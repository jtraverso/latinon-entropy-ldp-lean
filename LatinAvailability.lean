module

public import WeightedJensen
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Availability of a finite Latin rectangle. Histories are reverse lists
of row permutations, so adding the next row is list cons. -/

noncomputable section

namespace LatinonEntropy

open Finset

abbrev LatinHistory (n : ℕ) := List (Equiv.Perm (Fin n))

def usedSymbols {n : ℕ} (h : LatinHistory n) (i : Fin n) : Finset (Fin n) :=
  (h.map (fun sigma => sigma i)).toFinset

def LatinHistoryValid {n : ℕ} : LatinHistory n → Prop
  | [] => True
  | sigma::h => LatinHistoryValid h ∧ ∀ i, sigma i ∉ usedSymbols h i

def availability {n : ℕ} (h : LatinHistory n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j ∈ usedSymbols h i then 0 else 1

def rowPermutationMatrix {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => if sigma i = j then 1 else 0

theorem availability_binary {n : ℕ} (h : LatinHistory n) (i j : Fin n) :
    availability h i j = 0 ∨ availability h i j = 1 := by
  unfold availability
  split_ifs <;> simp

theorem availability_nonneg {n : ℕ} (h : LatinHistory n) (i j : Fin n) :
    0 ≤ availability h i j := by
  rcases availability_binary h i j with hz | ho
  · simpa only [hz] using (le_refl (0 : ℝ))
  · simpa only [ho] using (zero_le_one : (0 : ℝ) ≤ 1)

theorem valid_row_nodup {n : ℕ} {h : LatinHistory n} (hh : LatinHistoryValid h) (i : Fin n) :
    (h.map (fun sigma => sigma i)).Nodup := by
  induction h with
  | nil => simp
  | cons sigma h ih =>
    exact List.nodup_cons.mpr ⟨by simpa only [usedSymbols,List.mem_toFinset] using hh.2 i,ih hh.1⟩

theorem valid_col_nodup {n : ℕ} {h : LatinHistory n} (hh : LatinHistoryValid h) (j : Fin n) :
    (h.map (fun sigma => sigma.symm j)).Nodup := by
  induction h with
  | nil => simp
  | cons sigma h ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hh.1⟩
    intro hmem
    obtain ⟨tau,htau,he⟩ := List.mem_map.mp hmem
    apply hh.2 (sigma.symm j)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨tau,htau,?_⟩
    change tau.symm j = sigma.symm j at he
    have ht : tau (sigma.symm j) = j := by rw [← he,tau.apply_symm_apply]
    rw [ht,sigma.apply_symm_apply]

theorem usedSymbols_card {n : ℕ} {h : LatinHistory n} (hh : LatinHistoryValid h) (i : Fin n) :
    (usedSymbols h i).card = h.length := by
  simpa only [usedSymbols,List.length_map] using List.toFinset_card_of_nodup (valid_row_nodup hh i)

theorem valid_history_length_le {n : ℕ} (hn : 0 < n) {h : LatinHistory n}
    (hh : LatinHistoryValid h) : h.length ≤ n := by
  have hc := card_le_univ (usedSymbols h ⟨0,hn⟩)
  simpa only [usedSymbols_card hh,Fintype.card_fin] using hc

theorem availability_row {n : ℕ} {h : LatinHistory n} (hh : LatinHistoryValid h) (i : Fin n) :
    (∑ j, availability h i j) = (n : ℝ)-h.length := by
  have hu : (∑ j : Fin n, if j ∈ usedSymbols h i then (1 : ℝ) else 0) = (h.length : ℝ) := by
    simp only [sum_boole,filter_mem_eq_inter,univ_inter,usedSymbols_card hh]
  have hs : (∑ j, availability h i j) +
      (∑ j : Fin n, if j ∈ usedSymbols h i then (1 : ℝ) else 0) = n := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _j : Fin n, (1 : ℝ) := sum_congr rfl (fun j _ => by
        unfold availability
        split_ifs <;> norm_num)
      _ = _ := by simp
  linarith

theorem usedSymbols_col_iff {n : ℕ} (h : LatinHistory n) (i j : Fin n) :
    j ∈ usedSymbols h i ↔ i ∈ (h.map (fun sigma => sigma.symm j)).toFinset := by
  simp only [usedSymbols,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨sigma,hs,he⟩
    exact ⟨sigma,hs,(congrArg sigma.symm he).symm.trans (by simp)⟩
  · rintro ⟨sigma,hs,he⟩
    refine ⟨sigma,hs,?_⟩
    rw [← he,sigma.apply_symm_apply]

theorem availability_col {n : ℕ} {h : LatinHistory n} (hh : LatinHistoryValid h) (j : Fin n) :
    (∑ i, availability h i j) = (n : ℝ)-h.length := by
  have hc : (h.map (fun sigma => sigma.symm j)).toFinset.card = h.length := by
    simpa only [List.length_map] using List.toFinset_card_of_nodup (valid_col_nodup hh j)
  have he : ∀ i, availability h i j =
      if i ∈ (h.map (fun sigma => sigma.symm j)).toFinset then 0 else 1 := by
    intro i
    simp only [availability,usedSymbols_col_iff]
  have hu : (∑ i : Fin n, if i ∈ (h.map (fun sigma => sigma.symm j)).toFinset then (1 : ℝ) else 0) =
      (h.length : ℝ) := by simp only [sum_boole,filter_mem_eq_inter,univ_inter,hc]
  have hs : (∑ i, availability h i j) +
      (∑ i : Fin n, if i ∈ (h.map (fun sigma => sigma.symm j)).toFinset then (1 : ℝ) else 0) = n := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i : Fin n, (1 : ℝ) := sum_congr rfl (fun i _ => by rw [he]; split_ifs <;> norm_num)
      _ = _ := by simp
  linarith

theorem valid_cons_iff_available {n : ℕ} (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) :
    LatinHistoryValid (sigma::h) ↔ LatinHistoryValid h ∧ ∀ i, availability h i (sigma i) = 1 := by
  change (LatinHistoryValid h ∧ ∀ i, sigma i ∉ usedSymbols h i) ↔ _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  unfold availability
  by_cases hi : sigma i ∈ usedSymbols h i <;> simp [hi]

theorem availability_cons {n : ℕ} {h : LatinHistory n} {sigma : Equiv.Perm (Fin n)}
    (hh : LatinHistoryValid (sigma::h)) (i j : Fin n) :
    availability (sigma::h) i j = availability h i j-rowPermutationMatrix sigma i j := by
  have hi := hh.2 i
  by_cases hj : sigma i = j
  · subst j
    have hz : availability (sigma::h) i (sigma i) = 0 := by simp [availability,usedSymbols]
    have ho : availability h i (sigma i) = 1 := by simp only [availability,hi,ite_false]
    rw [hz,ho]
    simp [rowPermutationMatrix]
  · simp [availability,usedSymbols,rowPermutationMatrix,hj,Ne.symm hj]

end LatinonEntropy

#print axioms LatinonEntropy.availability_row
#print axioms LatinonEntropy.availability_col
#print axioms LatinonEntropy.availability_cons
