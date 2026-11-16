module

public import LatinMarginalStatistics

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

abbrev LatinBlock (r s q : ℕ) := (Fin r × Fin s) × Fin q

def latinBlockValue {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (xy : LatinCell n) (z : Fin n) : LatinBlock r s q :=
  ((row xy.1,col xy.2),sym z)

def latinBlockIndicator {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (b : LatinBlock r s q) (xy : LatinCell n) (z : Fin n) : ℝ :=
  if latinBlockValue row col sym xy z = b then 1 else 0

def latinBlockObservable {n r s q : ℕ} (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (b : LatinBlock r s q) (L : LatinArray n) : ℝ :=
  ∑ xy : LatinCell n, latinBlockIndicator row col sym b xy (latinCellValue xy L)

def latinLawBlockMass {n r s q : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) : ℝ :=
  ∑ xy : LatinCell n, ∑ z : Fin n,
    latinFamilyMarginal S w xy z*latinBlockIndicator row col sym b xy z

theorem latin_law_block_mass_as_observable {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    latinLawBlockMass S w row col sym b = ∑ L ∈ S, w L*latinBlockObservable row col sym b L :=
  latin_marginal_statistic S w (latinBlockIndicator row col sym b)

theorem latin_block_observable_relabel {n r s q : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) (g : symbolBlockStabilizer sym) (L : LatinArray n) :
    latinBlockObservable row col sym b (symbolRelabelEquiv g.val L) =
      latinBlockObservable row col sym b L := by
  unfold latinBlockObservable
  apply sum_congr rfl
  intro xy _
  have he : latinBlockValue row col sym xy (latinCellValue xy (symbolRelabelEquiv g.val L)) =
      latinBlockValue row col sym xy (latinCellValue xy L) :=
    Prod.ext rfl (symbol_relabel_preserves_block sym g L xy.1 xy.2)
  exact congrArg (fun k : LatinBlock r s q => if k = b then (1 : ℝ) else 0) he

theorem symbol_mixture_block_mass_eq {n r s q : ℕ} (S : Finset (LatinArray n))
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    latinLawBlockMass (symbolMixtureFamily sym S) (symbolMixtureWeight sym S) row col sym b =
      (∑ L ∈ S, latinBlockObservable row col sym b L)/(S.card : ℝ) := by
  let : Nonempty (symbolBlockStabilizer sym) := ⟨1⟩
  rw [latin_law_block_mass_as_observable,symbol_mixture_moment]
  simp_rw [latin_block_observable_relabel]
  rw [finiteMean_const]

theorem symbol_mixture_block_mass_preserved {n r s q : ℕ} (S : Finset (LatinArray n))
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    latinLawBlockMass (symbolMixtureFamily sym S) (symbolMixtureWeight sym S) row col sym b =
      latinLawBlockMass S (fun _ => 1/(S.card : ℝ)) row col sym b := by
  rw [symbol_mixture_block_mass_eq,latin_law_block_mass_as_observable,← mul_sum]
  ring

end LatinonEntropy

#print axioms LatinonEntropy.latin_law_block_mass_as_observable
#print axioms LatinonEntropy.latin_block_observable_relabel
#print axioms LatinonEntropy.symbol_mixture_block_mass_eq
#print axioms LatinonEntropy.symbol_mixture_block_mass_preserved
