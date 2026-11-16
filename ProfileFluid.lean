module

public import LatinAvailability

@[expose] public section

/-! The actual finite profile and hazard used by C3, including the terminal
indices. Remaining masses and hazards are constructed, not assumed. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

structure PositiveLatinProfile (n : ℕ) where
  npos : 0 < n
  p : Fin n → Fin n → Fin n → ℝ
  a : ℝ
  b : ℝ
  a_pos : 0 < a
  a_le_b : a ≤ b
  bounds : ∀ x i j, a/n ≤ p x i j ∧ p x i j ≤ b/n
  row_mass : ∀ x i, ∑ j, p x i j = 1
  col_mass : ∀ x j, ∑ i, p x i j = 1
  time_mass : ∀ i j, ∑ x, p x i j = 1

def profileTailSet (n t : ℕ) : Finset (Fin n) := univ.filter (fun x => t ≤ (x : ℕ))

theorem profileTailSet_card (n t : ℕ) : (profileTailSet n t).card = n-t := by
  by_cases ht : t < n
  · have he : profileTailSet n t = Ici (⟨t,ht⟩ : Fin n) := by ext x; simp [profileTailSet,Fin.le_def]
    rw [he,Fin.card_Ici]
  · have he : profileTailSet n t = ∅ := by
      ext x
      simp only [profileTailSet,mem_filter,mem_univ,true_and]
      simp only [Finset.notMem_empty,iff_false]
      have hx := x.isLt
      omega
    rw [he,card_empty,Nat.sub_eq_zero_of_le (le_of_not_gt ht)]

theorem profileTailSet_empty {n t : ℕ} (ht : n ≤ t) : profileTailSet n t = ∅ := by
  apply card_eq_zero.mp
  rw [profileTailSet_card,Nat.sub_eq_zero_of_le ht]

theorem profileTailSet_split {n t : ℕ} (ht : t < n) :
    profileTailSet n t = insert ⟨t,ht⟩ (profileTailSet n (t+1)) := by
  ext x
  simp only [profileTailSet,mem_filter,mem_univ,true_and,mem_insert,Fin.ext_iff]
  omega

def profileRemaining {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) : ℝ :=
  ∑ x ∈ profileTailSet n t, P.p x i j

def profileHazard {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) : ℝ :=
  if ht : t < n then P.p ⟨t,ht⟩ i j/profileRemaining P t i j else 0

namespace PositiveLatinProfile

variable {n : ℕ}

theorem entry_pos (P : PositiveLatinProfile n) (x i j : Fin n) : 0 < P.p x i j :=
  (div_pos P.a_pos (Nat.cast_pos.mpr P.npos)).trans_le (P.bounds x i j).1

theorem remaining_nonneg (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    0 ≤ profileRemaining P t i j := sum_nonneg (fun x _ => (P.entry_pos x i j).le)

theorem remaining_initial (P : PositiveLatinProfile n) (i j : Fin n) :
    profileRemaining P 0 i j = 1 := by simp [profileRemaining,profileTailSet,P.time_mass]

theorem remaining_terminal (P : PositiveLatinProfile n) (t : ℕ) (ht : n ≤ t) (i j : Fin n) :
    profileRemaining P t i j = 0 := by simp only [profileRemaining,profileTailSet_empty ht,sum_empty]

theorem entry_le_remaining (P : PositiveLatinProfile n) (t : ℕ) (ht : t < n) (i j : Fin n) :
    P.p ⟨t,ht⟩ i j ≤ profileRemaining P t i j := by
  exact single_le_sum (fun x _ => (P.entry_pos x i j).le) (by simp [profileTailSet])

theorem remaining_pos (P : PositiveLatinProfile n) (t : ℕ) (ht : t < n) (i j : Fin n) :
    0 < profileRemaining P t i j := (P.entry_pos ⟨t,ht⟩ i j).trans_le (P.entry_le_remaining t ht i j)

theorem remaining_le_one (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    profileRemaining P t i j ≤ 1 := by
  calc
    _ ≤ ∑ x, P.p x i j :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ => (P.entry_pos x i j).le)
    _ = 1 := P.time_mass i j

theorem remaining_split (P : PositiveLatinProfile n) (t : ℕ) (ht : t < n) (i j : Fin n) :
    profileRemaining P t i j = P.p ⟨t,ht⟩ i j+profileRemaining P (t+1) i j := by
  have hnot : (⟨t,ht⟩ : Fin n) ∉ profileTailSet n (t+1) := by simp [profileTailSet]
  rw [profileRemaining,profileTailSet_split ht,sum_insert hnot]
  rfl

theorem remaining_row (P : PositiveLatinProfile n) (t : ℕ) (i : Fin n) :
    (∑ j, profileRemaining P t i j) = ((n-t : ℕ) : ℝ) := by
  unfold profileRemaining
  rw [sum_comm]
  simp only [P.row_mass,sum_const,nsmul_eq_mul,mul_one,profileTailSet_card]

theorem remaining_col (P : PositiveLatinProfile n) (t : ℕ) (j : Fin n) :
    (∑ i, profileRemaining P t i j) = ((n-t : ℕ) : ℝ) := by
  unfold profileRemaining
  rw [sum_comm]
  simp only [P.col_mass,sum_const,nsmul_eq_mul,mul_one,profileTailSet_card]

theorem hazard_mem_unit (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    0 ≤ profileHazard P t i j ∧ profileHazard P t i j ≤ 1 := by
  by_cases ht : t < n
  · have hr := P.remaining_pos t ht i j
    simpa [profileHazard,ht] using And.intro (div_nonneg (P.entry_pos ⟨t,ht⟩ i j).le hr.le)
      ((div_le_one hr).mpr (P.entry_le_remaining t ht i j))
  · simp [profileHazard,ht]

theorem remaining_hazard (P : PositiveLatinProfile n) (t : ℕ) (ht : t < n) (i j : Fin n) :
    profileRemaining P t i j*profileHazard P t i j = P.p ⟨t,ht⟩ i j := by
  have hr := (P.remaining_pos t ht i j).ne'
  have he : profileHazard P t i j = P.p ⟨t,ht⟩ i j/profileRemaining P t i j := by
    simp [profileHazard,ht]
  rw [he]
  field_simp [hr]

theorem fluid_step (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    profileRemaining P (t+1) i j = profileRemaining P t i j*(1-profileHazard P t i j) := by
  by_cases ht : t < n
  · rw [mul_sub,mul_one,P.remaining_hazard t ht i j]
    linarith only [P.remaining_split t ht i j]
  · rw [P.remaining_terminal t (le_of_not_gt ht),P.remaining_terminal (t+1) (by omega),zero_mul]

theorem remaining_lower (P : PositiveLatinProfile n) (t : ℕ) (i j : Fin n) :
    ((n-t : ℕ) : ℝ)*(P.a/n) ≤ profileRemaining P t i j := by
  have h := sum_le_sum (fun x (_ : x ∈ profileTailSet n t) => (P.bounds x i j).1)
  simpa only [sum_const,nsmul_eq_mul,profileTailSet_card,profileRemaining] using h

theorem main_index (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps) (t : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-t) : t < n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have htR : (t : ℝ) < n := by nlinarith [mul_pos heps hnR]
  exact_mod_cast htR

theorem remaining_main_lower (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t) (i j : Fin n) :
    P.a*eps ≤ profileRemaining P t i j := by
  have ht := P.main_index eps heps t hdegree
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hl := P.remaining_lower t i j
  rw [Nat.cast_sub ht.le] at hl
  have hd := mul_le_mul_of_nonneg_right hdegree (div_nonneg P.a_pos.le hnR.le)
  have he : (eps*(n : ℝ))*(P.a/n) = P.a*eps := by field_simp
  rw [he] at hd
  exact hd.trans hl

theorem hazard_main_bounds (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t) (i j : Fin n) :
    P.a/n ≤ profileHazard P t i j ∧ profileHazard P t i j ≤ (P.b/(P.a*eps))/n := by
  have ht := P.main_index eps heps t hdegree
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hr := P.remaining_pos t ht i j
  have hlo := P.remaining_main_lower eps heps t hdegree i j
  have hAE : 0 < P.a*eps := mul_pos P.a_pos heps
  have hb : 0 ≤ P.b := P.a_pos.le.trans P.a_le_b
  have hc : 0 ≤ (P.b/(P.a*eps))/n := div_nonneg (div_nonneg hb hAE.le) hnR.le
  have hleft : ((P.b/(P.a*eps))/n)*(P.a*eps) = P.b/n := by
    field_simp [P.a_pos.ne',heps.ne',hnR.ne']
  have hu := mul_le_mul_of_nonneg_left hlo hc
  rw [hleft] at hu
  have hlow : P.a/n ≤ P.p ⟨t,ht⟩ i j/profileRemaining P t i j := by
    apply (le_div_iff₀ hr).mpr
    have hm := mul_le_mul_of_nonneg_left (P.remaining_le_one t i j) (div_nonneg P.a_pos.le hnR.le)
    have hh : (P.a/n)*profileRemaining P t i j ≤ P.a/n := by simpa only [mul_one] using hm
    exact hh.trans (P.bounds ⟨t,ht⟩ i j).1
  have hhigh : P.p ⟨t,ht⟩ i j/profileRemaining P t i j ≤ (P.b/(P.a*eps))/n :=
    (div_le_iff₀ hr).mpr ((P.bounds ⟨t,ht⟩ i j).2.trans hu)
  simpa [profileHazard,ht] using And.intro hlow hhigh

end PositiveLatinProfile

end LatinonEntropy

#print axioms LatinonEntropy.PositiveLatinProfile.fluid_step
#print axioms LatinonEntropy.PositiveLatinProfile.hazard_main_bounds
