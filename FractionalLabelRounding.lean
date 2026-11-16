module

public import FractionalLabelCost

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def FractionalLabelsClose {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (C : Fin t → Fin n × Fin n → ℝ)
    (tau : ℝ) (row : Fin n → Fin r) (col : Fin n → Fin s) : Prop :=
  (∀ a b k, |labelBlockError p q (C k) a b (row,col)| < tau) ∧
  (∀ a, |labelClassError p a row| < tau) ∧ (∀ b, |labelClassError q b col| < tau)

theorem abs_lt_of_sq_le_cost {u cost tau : ℝ} (htau : 0 < tau)
    (hu : u^2 ≤ cost) (hcost : cost < tau^2) : |u| < tau := by
  have h : |u|^2 < tau^2 := by simpa only [sq_abs] using hu.trans_lt hcost
  exact (sq_lt_sq₀ (abs_nonneg u) htau.le).mp h

/-- Simultaneous rounding under the actual product weights, obtained from
the proved second moments and total cost. Zero input probabilities are allowed. -/
theorem exists_fractional_label_rounding {n r s t : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hq : ∀ y b, 0 ≤ q y b)
    (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (C : Fin t → Fin n × Fin n → ℝ) (hC : ∀ k xy, 0 ≤ C k xy ∧ C k xy ≤ 1)
    (tau : ℝ) (htau : 0 < tau)
    (hlarge : (2*(r : ℝ)*(s : ℝ)*(t : ℝ)+(r : ℝ)+(s : ℝ))/(n : ℝ) < tau^2) :
    ∃ row col, 0 < pairedLabelWeight p q (row,col) ∧ FractionalLabelsClose p q C tau row col := by
  have hmean := (pairedLabel_rounding_cost_le hn p q hp hq hpt hqt C hC).trans_lt hlarge
  obtain ⟨omega,hw,hcost⟩ := finiteExpectation_exists_lt (pairedLabelWeight p q)
    (labelRoundingCost p q C) (pairedLabelWeight_nonneg p q hp hq)
    (pairedLabelWeight_total p q hpt hqt) (tau^2) hmean
  refine ⟨omega.1,omega.2,hw,?_,?_,?_⟩
  · intro a b k
    exact abs_lt_of_sq_le_cost htau (labelBlockError_sq_le_cost p q C omega a b k) hcost
  · intro a
    exact abs_lt_of_sq_le_cost htau (labelRowError_sq_le_cost p q C omega a) hcost
  · intro b
    exact abs_lt_of_sq_le_cost htau (labelColError_sq_le_cost p q C omega b) hcost

/-- One positive size threshold works for every stochastic pair of label
matrices and every bounded family of coefficient matrices of the fixed sizes. -/
theorem exists_uniform_fractional_label_rounding (r s t : ℕ) (tau : ℝ) (htau : 0 < tau) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ),
      (∀ x a, 0 ≤ p x a) → (∀ y b, 0 ≤ q y b) →
      (∀ x, ∑ a, p x a = 1) → (∀ y, ∑ b, q y b = 1) →
      ∀ C : Fin t → Fin n × Fin n → ℝ,
      (∀ k xy, 0 ≤ C k xy ∧ C k xy ≤ 1) →
      ∃ row col, 0 < pairedLabelWeight p q (row,col) ∧ FractionalLabelsClose p q C tau row col := by
  let K := 2*(r : ℝ)*(s : ℝ)*(t : ℝ)+(r : ℝ)+(s : ℝ)
  let N := max 1 (⌈K/tau^2⌉₊+1)
  have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn p q hp hq hpt hqt C hC
  have hnpos : 0 < n := hN.trans_le hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hceil : ⌈K/tau^2⌉₊ < n := Nat.lt_of_succ_le ((le_max_right _ _).trans hn)
  have hreal : K/tau^2 < (n : ℝ) := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hceil)
  have hlarge : K/(n : ℝ) < tau^2 := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ (sq_pos_of_pos htau)).mp hreal
    nlinarith only [h]
  exact exists_fractional_label_rounding hnpos p q hp hq hpt hqt C hC tau htau hlarge

end LatinonEntropy
