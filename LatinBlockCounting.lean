module

public import LatinBlockEntropy
public import SymbolMixtureEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- The entropy belongs to the mean block table of the original uniform
family. Invariance of that family under symbol permutations is not assumed. -/
theorem latin_block_count_log_upper {n r s q M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty)
    (hsize : ∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber sym a).card : ℝ)) :
    Real.log (S.card : ℝ) ≤
      (n : ℝ)^2*(Real.log (n : ℝ)-2+latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym)+
        (n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ)) := by
  have hs := symbol_mixture_count_entropy_upper hM sym S hS hsize
  have hb := latin_marginal_entropy_le_coarse hn (symbolMixtureFamily sym S)
    (symbolMixtureWeight sym S) (fun L hL => (symbolMixtureWeight_pos sym S hS L hL).le)
    (symbolMixtureWeight_total sym S hS) row col sym
  rw [symbol_mixture_coarse_entropy_preserved] at hb
  calc
    _ ≤ latinMarginalEntropy (symbolMixtureFamily sym S) (symbolMixtureWeight sym S)-
        2*(n : ℝ)^2+(n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ)) := hs
    _ ≤ ((n : ℝ)^2*Real.log (n : ℝ)+
        (n : ℝ)^2*latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym)-
        2*(n : ℝ)^2+(n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ)) := by linarith only [hb]
    _ = _ := by ring

/-- The exponential formulation includes empty families and never uses log 0. -/
theorem latin_block_count_exp_upper {n r s q M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (S : Finset (LatinArray n))
    (hsize : ∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber sym a).card : ℝ)) :
    (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*
      (Real.log (n : ℝ)-2+latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym)+
        (n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ))) := by
  by_cases hS : S.Nonempty
  · have hp : (0 : ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
    calc
      (S.card : ℝ) = Real.exp (Real.log (S.card : ℝ)) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (latin_block_count_log_upper hn hM row col sym S hS hsize)
  · have hz : S.card = 0 := Nat.eq_zero_of_not_pos (fun hp => hS (card_pos.mp hp))
    rw [hz,Nat.cast_zero]
    exact (Real.exp_pos _).le

theorem exists_latin_block_count_log_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n r s q : ℕ) (row : Fin n → Fin r)
      (col : Fin n → Fin s) (sym : Fin n → Fin q) (S : Finset (LatinArray n)),
      0 < n → S.Nonempty →
      (∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber sym a).card : ℝ)) →
      Real.log (S.card : ℝ) ≤ (n : ℝ)^2*
        (Real.log (n : ℝ)-2+latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym+eta) := by
  obtain ⟨M,hM,hcount⟩ := exists_symbol_mixture_entropy_threshold eta heta
  refine ⟨M,hM,?_⟩
  intro n r s q row col sym S hn hS hsize
  have hs := hcount n q sym S hS hsize
  have hb := latin_marginal_entropy_le_coarse hn (symbolMixtureFamily sym S)
    (symbolMixtureWeight sym S) (fun L hL => (symbolMixtureWeight_pos sym S hS L hL).le)
    (symbolMixtureWeight_total sym S hS) row col sym
  rw [symbol_mixture_coarse_entropy_preserved] at hb
  nlinarith only [hs,hb]

theorem exists_latin_block_count_exp_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n r s q : ℕ) (row : Fin n → Fin r)
      (col : Fin n → Fin s) (sym : Fin n → Fin q) (S : Finset (LatinArray n)),
      0 < n → (∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber sym a).card : ℝ)) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*
        (Real.log (n : ℝ)-2+latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym+eta)) := by
  obtain ⟨M,hM,hcount⟩ := exists_latin_block_count_log_threshold eta heta
  refine ⟨M,hM,?_⟩
  intro n r s q row col sym S hn hsize
  by_cases hS : S.Nonempty
  · have hp : (0 : ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
    calc
      (S.card : ℝ) = Real.exp (Real.log (S.card : ℝ)) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hcount n r s q row col sym S hn hS hsize)
  · have hz : S.card = 0 := Nat.eq_zero_of_not_pos (fun hp => hS (card_pos.mp hp))
    rw [hz,Nat.cast_zero]
    exact (Real.exp_pos _).le

end LatinonEntropy
