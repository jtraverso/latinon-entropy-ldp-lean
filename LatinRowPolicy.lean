module

public import FiniteHistory
public import LatinAvailability
public import PermanentalConcentration
public import PermanentReveal

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

structure LatinRowPolicy (n : ℕ) where
  matrix : LatinHistory n → Matrix (Fin n) (Fin n) ℝ
  nonneg : ∀ h i j, 0 ≤ matrix h i j
  row : ∀ h i, ∑ j, matrix h i j = 1
  col : ∀ h j, ∑ i, matrix h i j = 1
  support : ∀ h, LatinHistoryValid h → h.length < n →
    ∀ i j, availability h i j = 0 → matrix h i j = 0

def fallbackRowMatrix (n : ℕ) (h : LatinHistory n) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if LatinHistoryValid h ∧ h.length < n then
    availability h i j / ((n : ℝ)-h.length)
  else 1/(n : ℝ)

theorem fallbackRowMatrix_nonneg {n : ℕ} (h : LatinHistory n) (i j : Fin n) :
    0 ≤ fallbackRowMatrix n h i j := by
  by_cases hv : LatinHistoryValid h ∧ h.length < n
  · simp only [fallbackRowMatrix,hv]
    have ht : (h.length : ℝ) < n := by exact_mod_cast hv.2
    exact div_nonneg (availability_nonneg h i j) (by linarith)
  · simp only [fallbackRowMatrix,hv,ite_false]
    positivity

theorem fallbackRowMatrix_row {n : ℕ} (hn : 0 < n) (h : LatinHistory n) (i : Fin n) :
    (∑ j, fallbackRowMatrix n h i j) = 1 := by
  classical
  by_cases hv : LatinHistoryValid h ∧ h.length < n
  · have ht : (h.length : ℝ) < n := by exact_mod_cast hv.2
    have he : (∑ j, availability h i j/((n : ℝ)-h.length)) = 1 := by
      rw [← sum_div,availability_row hv.1,div_self (by linarith : (n : ℝ)-h.length ≠ 0)]
    simpa [fallbackRowMatrix,hv] using he
  · simp only [fallbackRowMatrix,hv,ite_false,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp

theorem fallbackRowMatrix_col {n : ℕ} (hn : 0 < n) (h : LatinHistory n) (j : Fin n) :
    (∑ i, fallbackRowMatrix n h i j) = 1 := by
  classical
  by_cases hv : LatinHistoryValid h ∧ h.length < n
  · have ht : (h.length : ℝ) < n := by exact_mod_cast hv.2
    have he : (∑ i, availability h i j/((n : ℝ)-h.length)) = 1 := by
      rw [← sum_div,availability_col hv.1,div_self (by linarith : (n : ℝ)-h.length ≠ 0)]
    simpa [fallbackRowMatrix,hv] using he
  · simp only [fallbackRowMatrix,hv,ite_false,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp

def fallbackRowPolicy (n : ℕ) (hn : 0 < n) : LatinRowPolicy n where
  matrix := fallbackRowMatrix n
  nonneg := fallbackRowMatrix_nonneg
  row := fallbackRowMatrix_row hn
  col := fallbackRowMatrix_col hn
  support := by
    intro h hh hlen i j hz
    simp only [fallbackRowMatrix,hh,hlen,and_self,ite_true,hz,zero_div]

namespace LatinRowPolicy

variable {n : ℕ}

theorem permanent_pos (P : LatinRowPolicy n) (hn : 0 < n) (h : LatinHistory n) : 0 < (P.matrix h).permanent :=
  (doubly_stochastic_permanent_log_lower hn (P.matrix h) (P.nonneg h) (P.row h) (P.col h)).1

def kernel (P : LatinRowPolicy n) (hn : 0 < n) : FiniteKernel (Equiv.Perm (Fin n)) where
  transition h sigma := permanentLaw (P.matrix h) sigma
  nonneg h sigma := permanentLaw_nonneg (P.matrix h) (P.nonneg h) (P.permanent_pos hn h) sigma
  total h := sum_permanentLaw (P.matrix h) (P.permanent_pos hn h).ne'

theorem positive_transition_valid (P : LatinRowPolicy n) (hn : 0 < n) {h : LatinHistory n} (hh : LatinHistoryValid h)
    (hlen : h.length < n) (sigma : Equiv.Perm (Fin n))
    (hs : 0 < (P.kernel hn).transition h sigma) : LatinHistoryValid (sigma::h) := by
  apply (valid_cons_iff_available h sigma).mpr
  refine ⟨hh,fun i => ?_⟩
  have hw : 0 < permWeight (P.matrix h) sigma :=
    (div_pos_iff_of_pos_right (P.permanent_pos hn h)).mp hs
  have hentry := positive_permWeight_entry (P.matrix h) (P.nonneg h) sigma hw i
  rcases availability_binary h i (sigma i) with hz | ho
  · rw [P.support h hh hlen i (sigma i) hz] at hentry
    exact False.elim (lt_irrefl _ hentry)
  · exact ho

theorem positive_history_valid (P : LatinRowPolicy n) (hn : 0 < n) (t : ℕ) (ht : t ≤ n) (h : LatinHistory n)
    (hlevel : h ∈ histories (Equiv.Perm (Fin n)) t)
    (hpos : 0 < historyWeight (P.kernel hn) h) : LatinHistoryValid h := by
  induction t generalizing h with
  | zero =>
    have he : h = [] := by simpa only [histories,mem_singleton] using hlevel
    simp [he,LatinHistoryValid]
  | succ t ih =>
    obtain ⟨g,hg,hm⟩ := mem_biUnion.mp hlevel
    obtain ⟨sigma,_,rfl⟩ := mem_image.mp hm
    change 0 < historyWeight (P.kernel hn) g*(P.kernel hn).transition g sigma at hpos
    have hw := pos_of_mul_pos_left hpos ((P.kernel hn).nonneg g sigma)
    have hs := pos_of_mul_pos_right hpos (historyWeight_nonneg (P.kernel hn) g)
    have hvalid := ih (by omega) g hg hw
    have hlen : g.length < n := by rw [histories_length hg]; omega
    exact P.positive_transition_valid hn hvalid hlen sigma hs

theorem completed_history_covers (P : LatinRowPolicy n) (hn : 0 < n) (h : LatinHistory n)
    (hlevel : h ∈ histories (Equiv.Perm (Fin n)) n)
    (hpos : 0 < historyWeight (P.kernel hn) h) :
    LatinHistoryValid h ∧ ∀ i, usedSymbols h i = univ := by
  have hv := P.positive_history_valid hn n le_rfl h hlevel hpos
  refine ⟨hv,fun i => ?_⟩
  apply eq_of_subset_of_card_le (subset_univ _)
  rw [card_univ,Fintype.card_fin,usedSymbols_card hv,histories_length hlevel]

theorem probability_valid_histories (P : LatinRowPolicy n) (hn : 0 < n) (t : ℕ) (ht : t ≤ n) :
    (∑ h ∈ (histories (Equiv.Perm (Fin n)) t).filter LatinHistoryValid,
      historyWeight (P.kernel hn) h) = 1 := by
  classical
  rw [sum_filter]
  calc
    _ = ∑ h ∈ histories (Equiv.Perm (Fin n)) t, historyWeight (P.kernel hn) h := by
      apply sum_congr rfl
      intro h hh
      split_ifs with hv
      · rfl
      · have hw : historyWeight (P.kernel hn) h = 0 :=
          le_antisymm (le_of_not_gt (fun hp => hv (P.positive_history_valid hn t ht h hh hp)))
            (historyWeight_nonneg (P.kernel hn) h)
        exact hw.symm
    _ = 1 := historyWeight_total _ _

end LatinRowPolicy

end LatinonEntropy

#print axioms LatinonEntropy.fallbackRowPolicy
#print axioms LatinonEntropy.LatinRowPolicy.probability_valid_histories
#print axioms LatinonEntropy.LatinRowPolicy.completed_history_covers
