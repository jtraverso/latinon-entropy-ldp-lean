module

public import EntropyWeights

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem profile_fluid_row_upper {n : ℕ} (P : PositiveLatinProfile n) (x : Fin n) :
    profileFluidRowEntropy P x.val ≤ (n : ℝ)*Real.log ((n : ℝ)-x.val) := by
  have hr : ∀ i, (∑ j, P.p x i j*Real.log (profileRemaining P x.val i j/P.p x i j)) ≤
      Real.log ((n : ℝ)-x.val) := by
    intro i
    have hpos : 0 < ∑ j, profileRemaining P x.val i j := by
      rw [P.remaining_row x.val i]
      exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt x.isLt)
    have hg := finite_gibbs (P.p x i) (profileRemaining P x.val i)
      (fun j => (P.entry_pos x i j).le) (fun j => P.remaining_nonneg x.val i j) (P.row_mass x i)
      (fun j _ => P.remaining_pos x.val x.isLt i j) hpos
    rw [P.remaining_row x.val i,Nat.cast_sub x.isLt.le] at hg
    have he : (∑ j, P.p x i j*Real.log (profileRemaining P x.val i j/P.p x i j)) =
        (∑ j, P.p x i j*Real.log (profileRemaining P x.val i j))-(∑ j, P.p x i j*Real.log (P.p x i j)) := by
      have hl : ∀ j, Real.log (profileRemaining P x.val i j/P.p x i j) =
          Real.log (profileRemaining P x.val i j)-Real.log (P.p x i j) := fun j =>
        Real.log_div (P.remaining_pos x.val x.isLt i j).ne' (P.entry_pos x i j).ne'
      simp_rw [hl]
      simp only [mul_sub,sum_sub_distrib]
    rw [he]
    linarith only [hg]
  rw [profile_fluid_row_eq]
  calc
    _ ≤ ∑ _i : Fin n, Real.log ((n : ℝ)-x.val) := sum_le_sum (fun i _ => hr i)
    _ = _ := by simp

theorem profile_fluid_row_upper_log_n {n : ℕ} (P : PositiveLatinProfile n) (x : Fin n) :
    profileFluidRowEntropy P x.val ≤ (n : ℝ)*Real.log (n : ℝ) := by
  have hx : (x.val : ℝ) < n := Nat.cast_lt.mpr x.isLt
  have hk : 0 < (n : ℝ)-x.val := sub_pos.mpr hx
  have hle : (n : ℝ)-x.val ≤ (n : ℝ) := by linarith only [Nat.cast_nonneg (α := ℝ) x.val]
  exact (profile_fluid_row_upper P x).trans (mul_le_mul_of_nonneg_left (Real.log_le_log hk hle) (Nat.cast_nonneg n))

end LatinonEntropy

#print axioms LatinonEntropy.profile_fluid_row_upper
