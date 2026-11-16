module

public import LatinBlockWindows
public import FiniteTableEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_coarse_entropy_eq_finite_table {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    latinLawCoarseEntropy S w row col sym =
      finiteTableEntropy (latinBlockVolume row col sym) (latinLawBlockTable S w row col sym) :=
  latin_coarse_entropy_eq_full_sum S w row col sym

/-- A local upper bound for actual families in fixed block-coordinate
windows. Both the entropy tolerance and the symbol-class threshold are
constructed; there is no hypothesis bounding the mean table's entropy. -/
theorem exists_latin_block_local_upper {r s q : ℕ}
    (volume target : LatinBlock r s q → ℝ) (hv : ∀ b, 0 < volume b)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, 0 < M ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ (n : ℕ) (row : Fin n → Fin r) (col : Fin n → Fin s)
        (sym : Fin n → Fin q) (S : Finset (LatinArray n)),
      0 < n → (∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber sym a).card : ℝ)) →
      (∀ b, |latinBlockVolume row col sym b-volume b| < delta) →
      (∀ L ∈ S, ∀ b, |latinBlockObservable row col sym b L/(n : ℝ)^2-target b| ≤ delta/2) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*
        (Real.log (n : ℝ)-2+finiteTableEntropy volume target+eta)) := by
  obtain ⟨M,hM,hcount⟩ := exists_latin_block_count_exp_threshold (eta/2) (half_pos heta)
  obtain ⟨delta,hd,hnear⟩ := finite_table_entropy_local_upper volume target hv (eta/2) (half_pos heta)
  refine ⟨M,hM,delta,hd,?_⟩
  intro n row col sym S hn hsize hvol hwindow
  by_cases hS : S.Nonempty
  · have hmean := latin_mean_block_window S hS row col sym target (delta/2) hwindow
    have hE : latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym ≤
        finiteTableEntropy volume target+eta/2 := by
      rw [latin_coarse_entropy_eq_finite_table]
      exact hnear _ _ hvol (fun b => (hmean b).trans_lt (half_lt_self hd))
    apply (hcount n r s q row col sym S hn hsize).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (n : ℝ))
    linarith only [hE]
  · have hz : S.card = 0 := Nat.eq_zero_of_not_pos (fun hp => hS (card_pos.mp hp))
    rw [hz,Nat.cast_zero]
    exact (Real.exp_pos _).le

end LatinonEntropy
