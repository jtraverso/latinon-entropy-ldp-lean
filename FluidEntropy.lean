module

public import ProfileFluid

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem log_potential_step (u v : ℝ) (hu : 0 < u) (hv : 0 ≤ v) :
    (u*Real.log u-u)-(v*Real.log v-v) ≤ (u-v)*Real.log u := by
  by_cases hz : v = 0
  · simp only [hz,zero_mul,sub_zero]
    linarith only [hu]
  · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hu hvp)) hv
    rw [Real.log_div hu.ne' hz] at h
    have he : v*(u/v-1) = u-v := by field_simp
    rw [he] at h
    nlinarith only [h]

def profileLogRemainingIncrement {n : ℕ} (P : PositiveLatinProfile n) (i j : Fin n) (t : ℕ) : ℝ :=
  if ht : t < n then P.p ⟨t,ht⟩ i j*Real.log (profileRemaining P t i j) else 0

theorem profile_log_remaining_partial {n : ℕ} (P : PositiveLatinProfile n) (i j : Fin n)
    (T : ℕ) (hT : T ≤ n) :
    (profileRemaining P 0 i j*Real.log (profileRemaining P 0 i j)-profileRemaining P 0 i j)-
      (profileRemaining P T i j*Real.log (profileRemaining P T i j)-profileRemaining P T i j) ≤
      ∑ t ∈ range T, profileLogRemainingIncrement P i j t := by
  induction T with
  | zero => simp
  | succ T ih =>
    have ht : T < n := by omega
    have hs := log_potential_step (profileRemaining P T i j) (profileRemaining P (T+1) i j)
      (P.remaining_pos T ht i j) (P.remaining_nonneg (T+1) i j)
    have hp := P.remaining_split T ht i j
    have he : profileRemaining P T i j-profileRemaining P (T+1) i j = P.p ⟨T,ht⟩ i j := by linarith only [hp]
    rw [he] at hs
    rw [sum_range_succ]
    have hinc : profileLogRemainingIncrement P i j T = P.p ⟨T,ht⟩ i j*Real.log (profileRemaining P T i j) := by
      simp only [profileLogRemainingIncrement,ht,dite_true]
    rw [hinc]
    have hi := ih (Nat.le_of_succ_le hT)
    linarith only [hs,hi]

theorem profile_log_remaining_sum {n : ℕ} (P : PositiveLatinProfile n) (i j : Fin n) :
    -1 ≤ ∑ x : Fin n, P.p x i j*Real.log (profileRemaining P x.val i j) := by
  have h := profile_log_remaining_partial P i j n le_rfl
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [P.remaining_initial,P.remaining_terminal n le_rfl,Real.log_one,mul_zero,zero_mul,
    sub_zero,sub_self,zero_sub,profileLogRemainingIncrement,Fin.is_lt,dite_true] using h

def profileEntropy {n : ℕ} (P : PositiveLatinProfile n) : ℝ :=
  -(∑ x, ∑ i, ∑ j, P.p x i j*Real.log (P.p x i j))

def profileFluidEntropy {n : ℕ} (P : PositiveLatinProfile n) : ℝ :=
  ∑ x, ∑ i, ∑ j, P.p x i j*Real.log (profileRemaining P x.val i j/P.p x i j)

theorem profile_fluid_entropy_lower {n : ℕ} (P : PositiveLatinProfile n) :
    profileEntropy P-(n : ℝ)^2 ≤ profileFluidEntropy P := by
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => profile_log_remaining_sum P i j))
  have he : (∑ x : Fin n, ∑ i, ∑ j, P.p x i j*Real.log (profileRemaining P x.val i j)) =
      ∑ i, ∑ j, ∑ x : Fin n, P.p x i j*Real.log (profileRemaining P x.val i j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
  have hbase : -(n : ℝ)^2 ≤ ∑ x : Fin n, ∑ i, ∑ j, P.p x i j*Real.log (profileRemaining P x.val i j) := by
    rw [he]
    calc
      _ = ∑ _i : Fin n, ∑ _j : Fin n, (-1 : ℝ) := by simp; ring
      _ ≤ _ := hsum
  have hid : profileFluidEntropy P = profileEntropy P+
      ∑ x : Fin n, ∑ i, ∑ j, P.p x i j*Real.log (profileRemaining P x.val i j) := by
    unfold profileFluidEntropy profileEntropy
    have hl : ∀ x i j, Real.log (profileRemaining P x.val i j/P.p x i j) =
        Real.log (profileRemaining P x.val i j)-Real.log (P.p x i j) :=
      fun x i j => Real.log_div (P.remaining_pos x.val x.isLt i j).ne' (P.entry_pos x i j).ne'
    simp_rw [hl]
    simp only [mul_sub,sum_sub_distrib]
    ring
  rw [hid]
  linarith only [hbase]

end LatinonEntropy

#print axioms LatinonEntropy.profile_log_remaining_sum
#print axioms LatinonEntropy.profile_fluid_entropy_lower
