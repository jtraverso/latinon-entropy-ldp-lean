module

public import FractionalLabelRounding
public import LatinBlockObservables

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def latinSymbolClassMatrix {n t : ℕ} (sym : Fin n → Fin t) (L : LatinArray n)
    (k : Fin t) (xy : Fin n × Fin n) : ℝ :=
  if sym (L.val xy.1 xy.2) = k then 1 else 0

def latinFractionalBlockTable {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (sym : Fin n → Fin t) (L : LatinArray n)
    (z : LatinBlock r s t) : ℝ :=
  fractionalBlockCount p q (latinSymbolClassMatrix sym L z.2) z.1.1 z.1.2/(n : ℝ)^2

theorem latinSymbolClassMatrix_bounds {n t : ℕ} (sym : Fin n → Fin t) (L : LatinArray n)
    (k : Fin t) (xy : Fin n × Fin n) :
    0 ≤ latinSymbolClassMatrix sym L k xy ∧ latinSymbolClassMatrix sym L k xy ≤ 1 := by
  unfold latinSymbolClassMatrix
  split_ifs <;> norm_num

theorem labelClassCount_eq_card {n r : ℕ} (row : Fin n → Fin r) (a : Fin r) :
    labelClassCount a row = ((univ.filter (fun x => row x = a)).card : ℝ) := by
  calc
    _ = ∑ x : Fin n, if row x = a then (1 : ℝ) else 0 := by
      unfold labelClassCount
      apply sum_congr rfl
      intro x _
      by_cases hx : row x = a
      · simp only [labelHit,hx,ite_true]
      · simp only [labelHit,hx,ite_false]
    _ = _ := by
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul,mul_one]

theorem labelBlockCount_eq_latin_observable {n r s t : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin t) (L : LatinArray n)
    (a : Fin r) (b : Fin s) (k : Fin t) :
    labelBlockCount (latinSymbolClassMatrix sym L k) a b (row,col) =
      latinBlockObservable row col sym ((a,b),k) L := by
  unfold labelBlockCount latinBlockObservable
  apply sum_congr rfl
  intro xy _
  unfold latinSymbolClassMatrix pairedCellHit labelHit latinBlockIndicator latinBlockValue latinCellValue
  by_cases hr : row xy.1 = a
  <;> by_cases hc : col xy.2 = b
  <;> by_cases hk : sym (L.val xy.1 xy.2) = k
  <;> simp_all

/-- Actual Latin block counts and actual class cardinalities are rounded
simultaneously. The order threshold is uniform in the square, fractional
assignments and prescribed symbol partition. -/
theorem exists_uniform_latin_fractional_rounding (r s t : ℕ) (tau : ℝ) (htau : 0 < tau) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ),
      (∀ x a, 0 ≤ p x a) → (∀ y b, 0 ≤ q y b) →
      (∀ x, ∑ a, p x a = 1) → (∀ y, ∑ b, q y b = 1) →
      ∀ (sym : Fin n → Fin t) (L : LatinArray n),
      ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col sym z L/(n : ℝ)^2-latinFractionalBlockTable p q sym L z| < tau) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-(∑ x, p x a)/(n : ℝ)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-(∑ y, q y b)/(n : ℝ)| < tau) := by
  obtain ⟨N,hN,hround⟩ := exists_uniform_fractional_label_rounding r s t tau htau
  refine ⟨N,hN,?_⟩
  intro n hn p q hp hq hpt hqt sym L
  obtain ⟨row,col,_,hclose⟩ := hround n hn p q hp hq hpt hqt (latinSymbolClassMatrix sym L)
    (latinSymbolClassMatrix_bounds sym L)
  rcases hclose with ⟨hb,hr,hc⟩
  refine ⟨row,col,?_,?_,?_⟩
  · intro z
    rcases z with ⟨⟨a,b⟩,k⟩
    simpa only [labelBlockError,labelBlockCount_eq_latin_observable,latinFractionalBlockTable] using hb a b k
  · intro a
    simpa only [labelClassError,labelClassCount_eq_card] using hr a
  · intro b
    simpa only [labelClassError,labelClassCount_eq_card] using hc b

end LatinonEntropy
