module

public import LatinBlockLocalUpper

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- A cover may use a different label for every element. Counting the
incidences pays only the number of labels, without choosing a common label. -/
theorem finite_label_cover_count_upper {A Labels : Type*} [Fintype Labels]
    (S : Finset A) (P : Labels → A → Prop) (B : ℝ)
    (hcover : ∀ a ∈ S, ∃ ell, P ell a)
    (hbound : ∀ ell, ((S.filter (P ell)).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ (Fintype.card Labels : ℝ)*B := by
  calc
    (S.card : ℝ) = ∑ _a ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ a ∈ S, ∑ ell : Labels, if P ell a then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro a ha
      obtain ⟨ell,hell⟩ := hcover a ha
      have h := single_le_sum (f := fun j : Labels => if P j a then (1 : ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (mem_univ ell)
      simpa only [hell,ite_true] using h
    _ = ∑ ell : Labels, ∑ a ∈ S, if P ell a then (1 : ℝ) else 0 := sum_comm
    _ = ∑ ell : Labels, ((S.filter (P ell)).card : ℝ) := by
      apply sum_congr rfl
      intro ell _
      rw [← sum_filter]
      simp
    _ ≤ ∑ _ell : Labels, B := sum_le_sum (fun ell _ => hbound ell)
    _ = _ := by simp

theorem latin_label_cover_count_upper (n r s : ℕ) (S : Finset (LatinArray n))
    (P : ((Fin n → Fin r) × (Fin n → Fin s)) → LatinArray n → Prop) (B : ℝ)
    (hcover : ∀ L ∈ S, ∃ ell, P ell L)
    (hbound : ∀ ell, ((S.filter (P ell)).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ ((r^n*s^n : ℕ) : ℝ)*B := by
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using
    finite_label_cover_count_upper S P B hcover hbound

theorem label_pair_card_exp_bound (r s n : ℕ) :
    ((r^n*s^n : ℕ) : ℝ) ≤ Real.exp ((n : ℝ)*((r : ℝ)+(s : ℝ))) := by
  have hr : (r : ℝ) ≤ Real.exp (r : ℝ) := by
    have h := Real.add_one_le_exp (r : ℝ)
    linarith only [h]
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by
    have h := Real.add_one_le_exp (s : ℝ)
    linarith only [h]
  calc
    _ = (r : ℝ)^n*(s : ℝ)^n := by rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow]
    _ ≤ (Real.exp (r : ℝ))^n*(Real.exp (s : ℝ))^n :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hr n)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hs n) (pow_nonneg (Nat.cast_nonneg _) n)
        (pow_nonneg (Real.exp_pos _).le n)
    _ = _ := by rw [mul_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul]

theorem exists_label_pair_subquadratic_bound (r s : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ((r^n*s^n : ℕ) : ℝ) ≤ Real.exp (eta*(n : ℝ)^2) := by
  refine ⟨⌈((r : ℝ)+(s : ℝ))/eta⌉₊+1,by omega,?_⟩
  intro n hn
  have hceil : ⌈((r : ℝ)+(s : ℝ))/eta⌉₊ ≤ n := (Nat.le_succ _).trans hn
  have hreal : ((r : ℝ)+(s : ℝ))/eta ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hceil)
  have hlinear : (r : ℝ)+(s : ℝ) ≤ eta*(n : ℝ) := by
    have h := (div_le_iff₀ heta).mp hreal
    nlinarith only [h]
  apply (label_pair_card_exp_bound r s n).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlinear (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [h]

end LatinonEntropy

#print axioms LatinonEntropy.finite_label_cover_count_upper
#print axioms LatinonEntropy.latin_label_cover_count_upper
#print axioms LatinonEntropy.label_pair_card_exp_bound
#print axioms LatinonEntropy.exists_label_pair_subquadratic_bound
