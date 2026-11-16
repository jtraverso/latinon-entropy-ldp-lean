module

public import FiniteAverages
public import Mathlib.Analysis.SpecialFunctions.Log.Sum

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def permanentCapError (m n : ℕ) : ℝ :=
  ((m : ℝ) + 1) * Real.log n + (m : ℝ) * (m + 1) + 1

/-- Explicit logarithmic error for the finite-label row-cap sum. There is no
asymptotic notation or permanent estimate among the hypotheses. -/
theorem finite_label_cap_sum (n m : ℕ) (hn : 0 < n) :
    (n : ℝ) * finiteMean (fun t : Fin n =>
      Real.log ((m : ℝ) / n + ((n : ℝ) - t) / n)) ≤
      -(n : ℝ) + permanentCapError m n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (m + n : ℕ) := by exact_mod_cast (Nat.add_pos_right m hn)
  have hN1 : (1 : ℝ) ≤ (m + n : ℕ) := by exact_mod_cast (Nat.add_pos_right m hn)
  have hs :
      (n : ℝ) * finiteMean (fun t : Fin n => Real.log ((m : ℝ) / n + ((n : ℝ) - t) / n)) =
      (∑ k ∈ range n, Real.log ((m : ℝ) + k + 1)) - n * Real.log n := by
    unfold finiteMean
    rw [Fintype.card_fin,mul_div_cancel₀ _ hnR.ne']
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      Real.log ((m : ℝ) / n + ((n : ℝ) - k) / n)) n]
    rw [← sum_range_reflect]
    calc
      (∑ k ∈ range n, Real.log ((m : ℝ) / n + ((n : ℝ) - (n - 1 - k : ℕ)) / n)) =
          ∑ k ∈ range n, (Real.log ((m : ℝ) + k + 1) - Real.log n) := by
        apply sum_congr rfl
        intro k hk
        have hkn : k < n := mem_range.mp hk
        have he : (m : ℝ) / n + ((n : ℝ) - (n - 1 - k : ℕ)) / n =
            ((m : ℝ) + k + 1) / n := by
          rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [he,Real.log_div (by positivity : (0 : ℝ) < (m : ℝ) + k + 1).ne' hnR.ne']
      _ = _ := by simp [sum_sub_distrib]
  rw [hs]
  have hshift : (∑ k ∈ range n, Real.log ((m : ℝ) + k + 1)) ≤
      Real.log ((m + n).factorial : ℝ) := by
    have hadd := sum_range_add (fun k : ℕ => Real.log ((k : ℝ) + 1)) m n
    have hpos : 0 ≤ ∑ k ∈ range m, Real.log ((k : ℝ) + 1) :=
      sum_nonneg (fun k _ => Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    have he : (∑ k ∈ range (m+n), Real.log ((k : ℝ)+1)) =
        (∑ k ∈ range m, Real.log ((k : ℝ)+1)) +
        (∑ k ∈ range n, Real.log ((m : ℝ)+k+1)) := by
      simpa only [Nat.cast_add] using hadd
    rw [Real.sum_log_add_one_eq_log_factorial] at he
    linarith
  have hfact := Real.sum_log_le hN1
  rw [Nat.floor_natCast,Real.sum_log_eq_log_factorial] at hfact
  have hlog : Real.log ((m+n : ℕ) : ℝ) ≤ Real.log n + (m : ℝ) / n := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN hnR)
    rw [Real.log_div hN.ne' hnR.ne'] at h
    have he : ((m+n : ℕ) : ℝ) / n - 1 = (m : ℝ) / n := by
      push_cast
      field_simp
      ring
    rw [he] at h
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ ((m+n : ℕ) : ℝ) + 1)
  have hinv : (m : ℝ) * (m + 1) / n ≤ (m : ℝ) * (m + 1) :=
    div_le_self (by positivity) hn1
  have he : (((m+n : ℕ) : ℝ) + 1) * (Real.log n + (m : ℝ) / n) -
      (m+n : ℕ) + 1 - n * Real.log n =
      -(n : ℝ) + ((m : ℝ)+1)*Real.log n + (m : ℝ)*(m+1)/n + 1 := by
    push_cast
    field_simp
    ring
  unfold permanentCapError
  nlinarith

end LatinonEntropy

#print axioms LatinonEntropy.finite_label_cap_sum
