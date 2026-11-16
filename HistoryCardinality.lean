module

public import FiniteHistory
public import LatinAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem histories_card_real {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (T : ℕ) :
    ((histories Ω T).card : ℝ) = (Fintype.card Ω : ℝ)^T := by
  induction T with
  | zero => simp [histories]
  | succ T ih =>
    have hs := history_sum_succ (Ω := Ω) T (fun _ => (1 : ℝ))
    simp only [sum_const,card_univ,nsmul_eq_mul] at hs
    simpa only [mul_one,ih,pow_succ] using hs

theorem latin_history_card_exp_bound (n : ℕ) (hn : 0 < n) :
    ((histories (Equiv.Perm (Fin n)) n).card : ℝ) ≤
      Real.exp ((n : ℝ)^2*Real.log (n : ℝ)) := by
  have hinj : Function.Injective (fun sigma : Equiv.Perm (Fin n) => fun i => sigma i) := by
    intro sigma tau he
    exact Equiv.ext (congrFun he)
  have hcard : Fintype.card (Equiv.Perm (Fin n)) ≤ n^n := by
    simpa only [Fintype.card_fun,Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  have hcardR : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast hcard
  rw [histories_card_real]
  calc
    _ ≤ ((n : ℝ)^n)^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardR n
    _ = Real.exp ((n : ℝ)^2*Real.log (n : ℝ)) := by
      have he : (n : ℝ)^2*Real.log (n : ℝ) = (n : ℝ)*((n : ℝ)*Real.log (n : ℝ)) := by ring
      rw [he,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (Nat.cast_pos.mpr hn)]

theorem latin_history_card_reference_cap (n : ℕ) (hn : 0 < n) :
    ((histories (Equiv.Perm (Fin n)) n).card : ℝ)*
      Real.exp (-((n : ℝ)^2*Real.log (n : ℝ))) ≤ 1 := by
  calc
    _ ≤ Real.exp ((n : ℝ)^2*Real.log (n : ℝ))*
        Real.exp (-((n : ℝ)^2*Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right (latin_history_card_exp_bound n hn) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end LatinonEntropy

#print axioms LatinonEntropy.latin_history_card_reference_cap
