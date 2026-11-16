module

public import PermanentalEntropy
public import ProfileProcess
public import FluidEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileEntropyWeight {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) : ℝ :=
  -(profileHazard P t i j*Real.log (profileHazard P t i j))

def profileLinearEntropy {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ)
    (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, B i j*profileEntropyWeight P t i j

def profileFluidRowEntropy {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ) : ℝ :=
  profileLinearEntropy P t (profileRemaining P t)

def profileEntropyWeightCap {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) : ℝ :=
  ((P.b/(P.a*eps))/n)*(Real.log (n : ℝ)+|Real.log P.a|)

theorem profileEntropyWeight_nonneg {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    0 ≤ profileEntropyWeight P t i j := by
  have hh := P.hazard_mem_unit t i j
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hh.1 (Real.log_nonpos hh.1 hh.2))

theorem profileEntropyWeightCap_nonneg {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps) :
    0 ≤ profileEntropyWeightCap P eps := by
  have hc : 0 ≤ P.b/(P.a*eps) := div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le
  exact mul_nonneg (div_nonneg hc (Nat.cast_nonneg n))
    (add_nonneg (Real.log_natCast_nonneg n) (abs_nonneg _))

theorem profileEntropyWeight_le_cap {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t) (i j : Fin n) :
    profileEntropyWeight P t i j ≤ profileEntropyWeightCap P eps := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hb := P.hazard_main_bounds eps heps t hdegree i j
  have hh := P.hazard_mem_unit t i j
  have hl := Real.log_le_log (div_pos P.a_pos hn) hb.1
  rw [Real.log_div P.a_pos.ne' hn.ne'] at hl
  have hlog : -Real.log (profileHazard P t i j) ≤ Real.log (n : ℝ)+|Real.log P.a| := by
    linarith only [hl,neg_abs_le (Real.log P.a)]
  have hnlog : 0 ≤ -Real.log (profileHazard P t i j) := neg_nonneg.mpr (Real.log_nonpos hh.1 hh.2)
  have hc : 0 ≤ (P.b/(P.a*eps))/n := div_nonneg
    (div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le) hn.le
  calc
    _ = profileHazard P t i j*(-Real.log (profileHazard P t i j)) := by unfold profileEntropyWeight; ring
    _ ≤ _ := mul_le_mul hb.2 hlog hnlog hc

theorem stoppedAvailability_mem_unit {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (i j : Fin n) :
    0 ≤ stoppedAvailability Good (profileHazard P) h i j ∧
      stoppedAvailability Good (profileHazard P) h i j ≤ 1 := by
  induction h with
  | nil => simp [stoppedAvailability,availability,usedSymbols]
  | cons sigma h ih =>
    by_cases hlive : historyLive Good h
    · simp only [stoppedAvailability,hlive,ite_true]
      rcases availability_binary (sigma::h) i j with hz | ho
      · simp [hz]
      · simp [ho]
    · simp only [stoppedAvailability,hlive,ite_false]
      have hh := P.hazard_mem_unit h.length i j
      have hnonneg : 0 ≤ 1-profileHazard P h.length i j := sub_nonneg.mpr hh.2
      refine ⟨mul_nonneg ih.1 hnonneg,?_⟩
      exact (mul_le_mul_of_nonneg_right ih.2 hnonneg).trans (by linarith only [hh.1])

theorem profile_linear_aux_entropy_bounds {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) :
    0 ≤ profileLinearEntropy P t (stoppedAvailability Good (profileHazard P) h) ∧
      profileLinearEntropy P t (stoppedAvailability Good (profileHazard P) h) ≤
        (n : ℝ)^2*profileEntropyWeightCap P eps := by
  constructor
  · exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => mul_nonneg
      (stoppedAvailability_mem_unit P Good h i j).1 (profileEntropyWeight_nonneg P t i j)))
  · calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, profileEntropyWeightCap P eps := by
        apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
        exact (mul_le_mul_of_nonneg_right (stoppedAvailability_mem_unit P Good h i j).2
          (profileEntropyWeight_nonneg P t i j)).trans (by
            simpa only [one_mul] using profileEntropyWeight_le_cap P eps heps t hdegree i j)
      _ = _ := by simp; ring

theorem profile_candidate_entropy_eq {n : ℕ} (P : PositiveLatinProfile n) (h : LatinHistory n) :
    matrixEntropy (profileCandidate P h) = profileLinearEntropy P h.length (availability h) := by
  have he : ∀ i j, (availability h i j*profileHazard P h.length i j)*
      Real.log (availability h i j*profileHazard P h.length i j) =
        availability h i j*(profileHazard P h.length i j*Real.log (profileHazard P h.length i j)) := by
    intro i j
    rcases availability_binary h i j with hz | ho
    · simp only [hz,zero_mul]
    · simp only [ho,one_mul]
  unfold matrixEntropy profileCandidate profileLinearEntropy profileEntropyWeight
  simp_rw [he]
  simp only [mul_neg,sum_neg_distrib]

theorem profile_fluid_row_eq {n : ℕ} (P : PositiveLatinProfile n) (x : Fin n) :
    profileFluidRowEntropy P x.val =
      ∑ i, ∑ j, P.p x i j*Real.log (profileRemaining P x.val i j/P.p x i j) := by
  unfold profileFluidRowEntropy profileLinearEntropy profileEntropyWeight
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  calc
    _ = -(profileRemaining P x.val i j*profileHazard P x.val i j)*Real.log (profileHazard P x.val i j) := by ring
    _ = -P.p x i j*Real.log (profileHazard P x.val i j) := by rw [P.remaining_hazard x.val x.isLt]
    _ = _ := by
      simp only [profileHazard,x.isLt,dite_true]
      rw [Real.log_div (P.entry_pos x i j).ne' (P.remaining_pos x.val x.isLt i j).ne',
        Real.log_div (P.remaining_pos x.val x.isLt i j).ne' (P.entry_pos x i j).ne']
      ring

theorem profile_fluid_entropy_eq_sum_rows {n : ℕ} (P : PositiveLatinProfile n) :
    profileFluidEntropy P = ∑ x : Fin n, profileFluidRowEntropy P x.val := by
  simp only [profileFluidEntropy,profile_fluid_row_eq]

end LatinonEntropy

#print axioms LatinonEntropy.profile_linear_aux_entropy_bounds
#print axioms LatinonEntropy.profile_candidate_entropy_eq
#print axioms LatinonEntropy.profile_fluid_entropy_eq_sum_rows
