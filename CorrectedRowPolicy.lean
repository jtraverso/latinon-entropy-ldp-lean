module

public import LatinRowPolicy
public import QuasirandomCorrection

@[expose] public section

/-! Instantiate the row policy with the actual correction theorem. The
guard checks its hypotheses on the current availability and candidate M;
when they fail, the policy uses the regular fallback matrix. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

structure RowCorrectionParameters where
  eps : ℝ
  rho : ℝ
  a : ℝ
  c : ℝ
  eps_pos : 0 < eps
  rho_pos : 0 < rho
  rho_le : rho ≤ 1
  a_pos : 0 < a
  a_le_c : a ≤ c

def RowCorrectionParameters.upper (p : RowCorrectionParameters) : ℝ := max p.c (16/(p.rho*p.eps))
def RowCorrectionParameters.lower (p : RowCorrectionParameters) : ℝ := min (p.a/2) (1/4)

structure CorrectableHistory {n : ℕ} (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n) : Prop where
  valid : LatinHistoryValid h
  degree : p.eps*n ≤ (n : ℝ)-h.length
  cut : ∀ S T : Finset (Fin n), p.rho*S.card*T.card-
    p.rho*p.eps*(n : ℝ)^2/(64*p.upper) ≤ rectMass (availability h) S T
  zero : ∀ i j, availability h i j = 0 → M h i j = 0
  entries : ∀ i j, availability h i j = 1 → p.a/n ≤ M h i j ∧ M h i j ≤ p.c/n

def RowCorrectionOutput {n : ℕ} (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, ∑ j, Q i j = 1) ∧ (∀ j, ∑ i, Q i j = 1) ∧ (∀ i j, 0 ≤ Q i j) ∧
  (∀ i j, availability h i j = 0 → Q i j = 0) ∧
  (∀ i j, availability h i j = 1 → p.lower/n ≤ Q i j ∧ Q i j ≤ p.upper/n) ∧
  (∑ i, ∑ j, |Q i j-M h i j|) ≤
    3*((∑ i, |(∑ j, M h i j)-1|)+∑ j, |(∑ i, M h i j)-1|)

theorem correctable_history_exists {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) : ∃ Q, RowCorrectionOutput p M h Q := by
  exact correction_lemma hn p.eps p.rho p.a p.c ((n : ℝ)-h.length)
    p.eps_pos p.rho_pos p.rho_le p.a_pos p.a_le_c (availability h) (M h)
    (availability_binary h) (availability_row hc.valid) (availability_col hc.valid)
    hc.degree hc.cut hc.zero hc.entries

def correctedRowMatrix {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n) :
    Matrix (Fin n) (Fin n) ℝ :=
  if hc : CorrectableHistory p M h then
    Classical.choose (correctable_history_exists hn p M h hc)
  else fallbackRowMatrix n h

theorem correctedRowMatrix_spec {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) : RowCorrectionOutput p M h (correctedRowMatrix hn p M h) := by
  simpa [correctedRowMatrix,hc] using Classical.choose_spec (correctable_history_exists hn p M h hc)

def correctedRowPolicy {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) : LatinRowPolicy n where
  matrix := correctedRowMatrix hn p M
  nonneg := by
    intro h i j
    by_cases hc : CorrectableHistory p M h
    · exact (correctedRowMatrix_spec hn p M h hc).2.2.1 i j
    · simpa [correctedRowMatrix,hc] using fallbackRowMatrix_nonneg h i j
  row := by
    intro h i
    by_cases hc : CorrectableHistory p M h
    · exact (correctedRowMatrix_spec hn p M h hc).1 i
    · simpa [correctedRowMatrix,hc] using fallbackRowMatrix_row hn h i
  col := by
    intro h j
    by_cases hc : CorrectableHistory p M h
    · exact (correctedRowMatrix_spec hn p M h hc).2.1 j
    · simpa [correctedRowMatrix,hc] using fallbackRowMatrix_col hn h j
  support := by
    intro h hh hlen i j hz
    by_cases hc : CorrectableHistory p M h
    · exact (correctedRowMatrix_spec hn p M h hc).2.2.2.1 i j hz
    · simpa [correctedRowMatrix,hc,fallbackRowPolicy] using (fallbackRowPolicy n hn).support h hh hlen i j hz

theorem correctedRowPolicy_cap {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) (i j : Fin n) :
    (correctedRowPolicy hn p M).matrix h i j ≤ p.upper/n := by
  change correctedRowMatrix hn p M h i j ≤ p.upper/n
  have hs := correctedRowMatrix_spec hn p M h hc
  rcases availability_binary h i j with hz | ho
  · rw [hs.2.2.2.1 i j hz]
    have hp : 0 ≤ p.upper := (p.a_pos.le.trans p.a_le_c).trans (le_max_left _ _)
    exact div_nonneg hp (Nat.cast_nonneg n)
  · exact (hs.2.2.2.2.1 i j ho).2

end LatinonEntropy

#print axioms LatinonEntropy.correctable_history_exists
#print axioms LatinonEntropy.correctedRowPolicy
#print axioms LatinonEntropy.correctedRowPolicy_cap
