module

public import SymbolIntervalPartition
public import LatinIntervalBoundary
public import LatinFractionalRounding
public import SymbolBlockEvaluation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Fractional row/column weights with the actual Lebesgue symbol intervals. -/
def latinIntervalFractionalTable {n r s t : ℕ} (P : SymbolIntervalPartition t)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (L : LatinArray n)
    (z : LatinBlock r s t) : ℝ :=
  latinIntervalWeightedCount L (fun x => p x z.1.1) (fun y => q y z.1.2)
    (P.left z.2) (P.right z.2)/(n : ℝ)^2

theorem latin_fractional_table_eq_interval_class {n r s t : ℕ} (P : SymbolIntervalPartition t)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (L : LatinArray n)
    (z : LatinBlock r s t) :
    latinFractionalBlockTable p q (P.color n) L z =
      latinIntervalClassWeightedCount L (fun x => p x z.1.1) (fun y => q y z.1.2)
        (P.left z.2) (P.right z.2)/(n : ℝ)^2 := by
  unfold latinFractionalBlockTable fractionalBlockCount latinIntervalClassWeightedCount
  apply congrArg (fun a : ℝ => a/(n : ℝ)^2)
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  unfold latinSymbolClassMatrix symbolFloorIndicator
  by_cases hk : P.color n (L.val x y) = z.2
  · have hm := (P.color_eq_iff n (L.val x y) z.2).mp hk
    simp only [hk,hm,ite_true,one_mul,mul_one]
  · have hm : L.val x y ∉ symbolIntervalClass n (P.left z.2) (P.right z.2) :=
      fun h => hk ((P.color_eq_iff n (L.val x y) z.2).mpr h)
    simp only [hk,hm,ite_false,zero_mul,mul_zero]

theorem latin_interval_fractional_table_boundary_error {n r s t : ℕ} (hn : 0 < n)
    (P : SymbolIntervalPartition t) (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hq : ∀ y b, 0 ≤ q y b)
    (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (L : LatinArray n) (z : LatinBlock r s t) :
    |latinIntervalFractionalTable P p q L z-latinFractionalBlockTable p q (P.color n) L z| ≤
      2/(n : ℝ) := by
  rw [latin_fractional_table_eq_interval_class]
  exact latin_interval_boundary_error_normalized hn L _ _
    (fun x => ⟨hp x z.1.1,label_probability_le_one p hp hpt x z.1.1⟩)
    (fun y => ⟨hq y z.1.2,label_probability_le_one q hq hqt y z.1.2⟩)
    _ _ (P.left_nonneg z.2) ((P.left_nonneg z.2).trans (P.left_lt_right z.2).le)

theorem symbol_interval_colorFiber {n t : ℕ} (P : SymbolIntervalPartition t) (a : Fin n) :
    symbolColorFiber (P.color n) a =
      symbolIntervalClass n (P.left (P.color n a)) (P.right (P.color n a)) := by
  exact P.color_fiber n (P.color n a)

theorem exists_symbol_interval_colorFiber_size_threshold {t : ℕ}
    (P : SymbolIntervalPartition t) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ a : Fin n,
      (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ) := by
  obtain ⟨N,hN,hsize⟩ := P.exists_color_class_size_threshold M
  refine ⟨N,hN,?_⟩
  intro n hn a
  exact hsize n hn (P.color n a)

/-- Whole-symbol classes round actual interval-weighted statistics, with
one order threshold before all stochastic matrices and all Latin squares.
The boundary error and the symbol-fiber size hypotheses are discharged. -/
theorem exists_uniform_latin_interval_rounding {t : ℕ} (P : SymbolIntervalPartition t)
    (r s : ℕ) (tau : ℝ) (htau : 0 < tau) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ),
      (∀ x a, 0 ≤ p x a) → (∀ y b, 0 ≤ q y b) →
      (∀ x, ∑ a, p x a = 1) → (∀ y, ∑ b, q y b = 1) →
      ∀ L : LatinArray n, ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
            latinIntervalFractionalTable P p q L z| < tau) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-
          (∑ x, p x a)/(n : ℝ)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-
          (∑ y, q y b)/(n : ℝ)| < tau) ∧
        (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ)) := by
  obtain ⟨Nr,hNr,hround⟩ := exists_uniform_latin_fractional_rounding r s t (tau/2) (half_pos htau)
  obtain ⟨Ns,_,hsize⟩ := exists_symbol_interval_colorFiber_size_threshold P M
  obtain ⟨K,hK⟩ := exists_nat_gt (4/tau)
  refine ⟨max Nr (max Ns K),hNr.trans_le (le_max_left _ _),?_⟩
  intro n hn p q hp hq hpt hqt L
  have hNrn : Nr ≤ n := (le_max_left _ _).trans hn
  have hNsn : Ns ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hKn : K ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := hNr.trans_le hNrn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hlarge : (4 : ℝ) < (n : ℝ)*tau :=
    (div_lt_iff₀ htau).mp (hK.trans_le (Nat.cast_le.mpr hKn))
  have hsmall : 2/(n : ℝ) < tau/2 := by
    apply (div_lt_iff₀ hnR).mpr
    nlinarith only [hlarge]
  obtain ⟨row,col,hb,hr,hc⟩ := hround n hNrn p q hp hq hpt hqt (P.color n) L
  refine ⟨row,col,?_,?_,?_,hsize n hNsn⟩
  · intro z
    have hboundary : |latinFractionalBlockTable p q (P.color n) L z-
        latinIntervalFractionalTable P p q L z| ≤ 2/(n : ℝ) := by
      rw [abs_sub_comm]
      exact latin_interval_fractional_table_boundary_error hnpos P p q hp hq hpt hqt L z
    have htriangle := abs_sub_le (latinBlockObservable row col (P.color n) z L/(n : ℝ)^2)
      (latinFractionalBlockTable p q (P.color n) L z) (latinIntervalFractionalTable P p q L z)
    have hroundz := hb z
    linarith only [htriangle,hboundary,hroundz,hsmall]
  · intro a
    exact (hr a).trans (half_lt_self htau)
  · intro b
    exact (hc b).trans (half_lt_self htau)

end LatinonEntropy

#print axioms LatinonEntropy.latin_fractional_table_eq_interval_class
#print axioms LatinonEntropy.latin_interval_fractional_table_boundary_error
#print axioms LatinonEntropy.symbol_interval_colorFiber
#print axioms LatinonEntropy.exists_symbol_interval_colorFiber_size_threshold
#print axioms LatinonEntropy.exists_uniform_latin_interval_rounding
#print axioms LatinonEntropy.symbolIntervalWeight_formula
#print axioms LatinonEntropy.symbolIntervalWeight_nonneg
#print axioms LatinonEntropy.symbolIntervalWeight_le_one
#print axioms LatinonEntropy.symbolIntervalWeight_eq_indicator_off_boundary
#print axioms LatinonEntropy.symbolIntervalClass_card
#print axioms LatinonEntropy.symbolIntervalClass_card_error
#print axioms LatinonEntropy.symbolIntervalClass_proportion_error
#print axioms LatinonEntropy.exists_symbolIntervalClass_size_threshold
#print axioms LatinonEntropy.symbolIntervalWeight_indicator_error
#print axioms LatinonEntropy.latin_row_nat_symbol_sum_le_one
#print axioms LatinonEntropy.latin_boundary_symbol_sum_le
#print axioms LatinonEntropy.latin_interval_boundary_error
#print axioms LatinonEntropy.latin_interval_boundary_error_normalized
#print axioms LatinonEntropy.SymbolIntervalPartition.exists_class
#print axioms LatinonEntropy.SymbolIntervalPartition.class_unique
#print axioms LatinonEntropy.SymbolIntervalPartition.color_eq_iff
#print axioms LatinonEntropy.SymbolIntervalPartition.color_class_proportion_error
#print axioms LatinonEntropy.SymbolIntervalPartition.exists_color_class_size_threshold

example : Nonempty (LatinonEntropy.SymbolIntervalPartition 1) := by
  refine ⟨{
    q_pos := by norm_num
    cut := fun i => (i.val : ℝ)
    strict := ?_
    first := by norm_num
    last := by norm_num
  }⟩
  intro i j hij
  exact Nat.cast_lt.mpr (show i.val < j.val from hij)
