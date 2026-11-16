module

public import LatinBlockObservables
public import FiniteEntropyPartition

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

abbrev LatinTriple (n : ℕ) := LatinCell n × Fin n

def latinTripleBlock {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (t : LatinTriple n) : LatinBlock r s q :=
  latinBlockValue row col sym t.1 t.2

def latinBlockFiber {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (b : LatinBlock r s q) : Finset (LatinTriple n) :=
  finiteImageFiber univ (latinTripleBlock row col sym) b

def latinActiveBlocks {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) : Finset (LatinBlock r s q) :=
  (univ : Finset (LatinTriple n)).image (latinTripleBlock row col sym)

def latinTripleWeight {n : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (t : LatinTriple n) : ℝ := latinFamilyMarginal S w t.1 t.2

def latinBlockVolume {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (b : LatinBlock r s q) : ℝ :=
  ((latinBlockFiber row col sym b).card : ℝ)/(n : ℝ)^3

def latinLawBlockTable {n r s q : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) : ℝ := latinLawBlockMass S w row col sym b/(n : ℝ)^2

def latinLawCoarseEntropy {n r s q : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) : ℝ :=
  ∑ b ∈ latinActiveBlocks row col sym, latinLawBlockTable S w row col sym b*
    Real.log (latinBlockVolume row col sym b/latinLawBlockTable S w row col sym b)

theorem latin_law_block_mass_eq_fiber_sum {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    latinLawBlockMass S w row col sym b = ∑ t ∈ latinBlockFiber row col sym b, latinTripleWeight S w t := by
  unfold latinBlockFiber finiteImageFiber
  rw [sum_filter,Fintype.sum_prod_type]
  unfold latinLawBlockMass
  apply sum_congr rfl
  intro xy _
  apply sum_congr rfl
  intro z _
  by_cases hb : latinBlockValue row col sym xy z = b
  · simp only [latinBlockIndicator,latinTripleBlock,latinTripleWeight,hb,ite_true,mul_one]
  · simp only [latinBlockIndicator,latinTripleBlock,latinTripleWeight,hb,ite_false,mul_zero]

theorem latin_triple_weight_total {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (htotal : ∑ L ∈ S, w L = 1) :
    (∑ t : LatinTriple n, latinTripleWeight S w t) = (n : ℝ)^2 := by
  simp only [latinTripleWeight,Fintype.sum_prod_type,latinFamilyMarginal_total,htotal,
    sum_const,card_univ,nsmul_eq_mul,mul_one]
  simp only [LatinCell,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  ring

theorem latin_marginal_entropy_eq_triple_sum {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) :
    latinMarginalEntropy S w = -(∑ t : LatinTriple n,
      latinTripleWeight S w t*Real.log (latinTripleWeight S w t)) := by
  simp only [latinMarginalEntropy,latinTripleWeight,Fintype.sum_prod_type]

end LatinonEntropy
