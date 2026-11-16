module

public import LatinonPatternConjecture

@[expose] public section

/-! Labelled one-factorizations of the complete ordered bipartite graph.
The factors are actual sets of edges, rather than another name for Latin arrays. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Each edge has one colour; each colour meets each vertex exactly once. -/
@[ext] structure LabelledBipartiteFactorization (n : ℕ) where
  factor : Fin n → Finset (Fin n × Fin n)
  edge_unique : ∀ x y, ∃! z, (x,y) ∈ factor z
  right_unique : ∀ z x, ∃! y, (x,y) ∈ factor z
  left_unique : ∀ z y, ∃! x, (x,y) ∈ factor z

def latinToFactorization {n : ℕ} (L : LatinArray n) : LabelledBipartiteFactorization n where
  factor z := univ.filter fun p => L.val p.1 p.2 = z
  edge_unique x y := by simp
  right_unique z x := by
    obtain ⟨y,hy⟩ := (L.property.1 x).2 z
    refine ⟨y,by simpa using hy,?_⟩
    intro y' hy'
    have hy'' : L.val x y' = z := by simpa using hy'
    exact (L.property.1 x).1 (hy''.trans hy.symm)
  left_unique z y := by
    obtain ⟨x,hx⟩ := (L.property.2 y).2 z
    refine ⟨x,by simpa using hx,?_⟩
    intro x' hx'
    have hx'' : L.val x' y = z := by simpa using hx'
    exact (L.property.2 y).1 (hx''.trans hx.symm)

def factorizationColour {n : ℕ} (F : LabelledBipartiteFactorization n) (x y : Fin n) : Fin n :=
  (F.edge_unique x y).choose

theorem factorizationColour_mem {n : ℕ} (F : LabelledBipartiteFactorization n) (x y : Fin n) :
    (x,y) ∈ F.factor (factorizationColour F x y) :=
  (F.edge_unique x y).choose_spec.1

theorem factorizationColour_eq_iff {n : ℕ} (F : LabelledBipartiteFactorization n) (x y z : Fin n) :
    factorizationColour F x y = z ↔ (x,y) ∈ F.factor z := by
  constructor
  · intro h; rw [← h]; exact factorizationColour_mem F x y
  · intro h
    exact ((F.edge_unique x y).choose_spec.2 z h).symm

def factorizationToLatin {n : ℕ} (F : LabelledBipartiteFactorization n) : LatinArray n := by
  refine ⟨factorizationColour F,?_,?_⟩
  · intro x
    constructor
    · intro y y' h
      change factorizationColour F x y = factorizationColour F x y' at h
      have hm := factorizationColour_mem F x y'
      rw [← h] at hm
      exact (F.right_unique (factorizationColour F x y) x).unique
        (factorizationColour_mem F x y) hm
    · intro z
      obtain ⟨y,hy,-⟩ := F.right_unique z x
      exact ⟨y,(factorizationColour_eq_iff F x y z).mpr hy⟩
  · intro y
    constructor
    · intro x x' h
      change factorizationColour F x y = factorizationColour F x' y at h
      have hm := factorizationColour_mem F x' y
      rw [← h] at hm
      exact (F.left_unique (factorizationColour F x y) y).unique
        (factorizationColour_mem F x y) hm
    · intro z
      obtain ⟨x,hx,-⟩ := F.left_unique z y
      exact ⟨x,(factorizationColour_eq_iff F x y z).mpr hx⟩

theorem factorizationToLatin_latinToFactorization {n : ℕ} (L : LatinArray n) :
    factorizationToLatin (latinToFactorization L) = L := by
  apply Subtype.ext
  funext x y
  exact (factorizationColour_eq_iff (latinToFactorization L) x y (L.val x y)).mpr (by simp [latinToFactorization])

theorem latinToFactorization_factorizationToLatin {n : ℕ} (F : LabelledBipartiteFactorization n) :
    latinToFactorization (factorizationToLatin F) = F := by
  apply LabelledBipartiteFactorization.ext
  funext z
  ext p
  simp only [latinToFactorization,mem_filter,mem_univ,true_and]
  exact factorizationColour_eq_iff F p.1 p.2 z

/-- The correspondence retains the orders on both vertex classes and colours. -/
def latinFactorizationEquiv (n : ℕ) : LatinArray n ≃ LabelledBipartiteFactorization n where
  toFun := latinToFactorization
  invFun := factorizationToLatin
  left_inv := factorizationToLatin_latinToFactorization
  right_inv := latinToFactorization_factorizationToLatin

def factorizationFamily {n : ℕ} (A : Finset (LatinArray n)) :
    Finset (LabelledBipartiteFactorization n) := A.image latinToFactorization

theorem card_factorizationFamily {n : ℕ} (A : Finset (LatinArray n)) :
    (factorizationFamily A).card = A.card :=
  card_image_iff.mpr (latinFactorizationEquiv n).injective.injOn

theorem mem_factorizationFamily_iff {n : ℕ} (F : LabelledBipartiteFactorization n)
    (A : Finset (LatinArray n)) : F ∈ factorizationFamily A ↔ factorizationToLatin F ∈ A := by
  constructor
  · rintro h
    obtain ⟨L,hL,rfl⟩ := mem_image.mp h
    simpa only [factorizationToLatin_latinToFactorization] using hL
  · intro h
    exact mem_image.mpr ⟨factorizationToLatin F,h,latinToFactorization_factorizationToLatin F⟩

/-- The complete local entropy formula for labelled factorizations of K_(n,n). -/
theorem finite_rate_factorization_entropy_count (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        ((factorizationFamily (latinonBallLatinFamily (hN.trans_le hn) W rho)).card : ℝ) ∧
      ((factorizationFamily (latinonBallLatinFamily (hN.trans_le hn) W rho)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal+eta)) := by
  simpa only [card_factorizationFamily] using
    finite_rate_latinon_entropy_count W hfinite r eta hr heta

/-- Finite pattern restrictions transfer with exactly the same normalization. -/
theorem finite_rate_factorization_pattern_log_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      0 < (factorizationFamily (standardMatrixPatternBoxFamily P z rho n)).card ∧
      |Real.log ((factorizationFamily (standardMatrixPatternBoxFamily P z rho n)).card : ℝ)/(n : ℝ)^2-
        (Real.log (n : ℝ)-2)+(latinonContractedRate (latinonPatternProfile P) z).toReal| ≤ eta := by
  simpa only [card_factorizationFamily] using
    finite_rate_standard_pattern_log_count P z hfinite r eta hr heta

end LatinonEntropy

#print axioms LatinonEntropy.factorizationColour_mem
#print axioms LatinonEntropy.factorizationColour_eq_iff
#print axioms LatinonEntropy.factorizationToLatin_latinToFactorization
#print axioms LatinonEntropy.latinToFactorization_factorizationToLatin
#print axioms LatinonEntropy.card_factorizationFamily
#print axioms LatinonEntropy.mem_factorizationFamily_iff
#print axioms LatinonEntropy.finite_rate_factorization_entropy_count
#print axioms LatinonEntropy.finite_rate_factorization_pattern_log_count
