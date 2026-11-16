module

public import SeriesCDR.Basic
public import HistoryLatinArray
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Replacement of distinguished Latin blocks in actual strictly bicoloured
Steiner triple systems. All completion data are explicit: a base STS contains
one packing, and every replacement packing has exactly the same pair footprint.
The theorem does not assume an entropy-preserving completion theorem. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def pairFootprint {V : Type*} [DecidableEq V] (P : Finset (Finset V)) (x y : V) : Prop :=
  ∃ B ∈ P, x ∈ B ∧ y ∈ B

def pairPacking {V : Type*} [DecidableEq V] (P : Finset (Finset V)) : Prop :=
  ∀ B ∈ P, ∀ C ∈ P, ∀ x y, x ≠ y → x ∈ B → y ∈ B → x ∈ C → y ∈ C → B = C

/-- The elementary completion step: replacing a packing with the same covered
pairs preserves the Steiner property, using the old residual blocks verbatim. -/
def replaceSteinerPacking {V : Type*} [DecidableEq V] (S : CDRBicolour.STS V)
    (P₀ P : Finset (Finset V)) (hbase : P₀ ⊆ S.blocks)
    (hcard : ∀ B ∈ P, B.card = 3) (hpack : pairPacking P)
    (hfoot : ∀ x y, x ≠ y → (pairFootprint P x y ↔ pairFootprint P₀ x y)) :
    CDRBicolour.STS V where
  blocks := (S.blocks \ P₀) ∪ P
  card_eq_three B hB := by
    rcases mem_union.mp hB with hB | hB
    · exact S.card_eq_three B (mem_sdiff.mp hB).1
    · exact hcard B hB
  existsUnique_block x y hxy := by
    by_cases hp : pairFootprint P x y
    · obtain ⟨B,hB,hx,hy⟩ := hp
      obtain ⟨B₀,hB₀,hx₀,hy₀⟩ := (hfoot x y hxy).mp ⟨B,hB,hx,hy⟩
      refine ⟨B,⟨mem_union_right _ hB,hx,hy⟩,?_⟩
      rintro C ⟨hC,hxC,hyC⟩
      rcases mem_union.mp hC with hC | hC
      · have he : C = B₀ := (S.existsUnique_block x y hxy).unique
          ⟨(mem_sdiff.mp hC).1,hxC,hyC⟩ ⟨hbase hB₀,hx₀,hy₀⟩
        exact False.elim ((mem_sdiff.mp hC).2 (he.symm ▸ hB₀))
      · exact hpack C hC B hB x y hxy hxC hyC hx hy
    · obtain ⟨B,hB,hunique⟩ := S.existsUnique_block x y hxy
      have hn : B ∉ P₀ := by
        intro h
        exact hp ((hfoot x y hxy).mpr ⟨B,h,hB.2⟩)
      refine ⟨B,⟨mem_union_left _ (mem_sdiff.mpr ⟨hB.1,hn⟩),hB.2⟩,?_⟩
      rintro C ⟨hC,hxC,hyC⟩
      rcases mem_union.mp hC with hC | hC
      · exact hunique C ⟨(mem_sdiff.mp hC).1,hxC,hyC⟩
      · exact False.elim (hp ⟨C,hC,hxC,hyC⟩)

theorem replaceSteinerPacking_bicoloured {V : Type*} [DecidableEq V]
    (S : CDRBicolour.STS V) (col : V → Fin 3)
    (P₀ P : Finset (Finset V)) (hbase : P₀ ⊆ S.blocks)
    (hcard : ∀ B ∈ P, B.card = 3) (hpack : pairPacking P)
    (hfoot : ∀ x y, x ≠ y → (pairFootprint P x y ↔ pairFootprint P₀ x y))
    (hS : CDRBicolour.IsStrictBicolouring S col)
    (hcol : ∀ B ∈ P, (B.image col).card = 2) :
    CDRBicolour.IsStrictBicolouring (replaceSteinerPacking S P₀ P hbase hcard hpack hfoot) col := by
  intro B hB
  rcases mem_union.mp hB with hB | hB
  · exact hS B (mem_sdiff.mp hB).1
  · exact hcol B hB

def chartLatinBlock {V : Type*} [DecidableEq V] {n : ℕ}
    (e : (Fin 3 × Fin n) ↪ V) (L : LatinArray n) (x y : Fin n) : Finset V :=
  {e (0,x),e (1,y),e (2,L.val x y)}

/-- The third point in the row-column block determines the Latin entry. -/
theorem chartLatinBlock_symbol_eq {V : Type*} [DecidableEq V] {n : ℕ}
    (e : (Fin 3 × Fin n) ↪ V) (L M : LatinArray n) (x y : Fin n)
    (h : chartLatinBlock e L x y = chartLatinBlock e M x y) : L.val x y = M.val x y := by
  have hz : e (2,L.val x y) ∈ chartLatinBlock e M x y := by
    rw [← h]; simp [chartLatinBlock]
  simp only [chartLatinBlock,mem_insert,mem_singleton] at hz
  rcases hz with hz | hz | hz
  · have hf := congrArg Prod.fst (e.injective hz)
    norm_num at hf
  · have hf := congrArg Prod.fst (e.injective hz)
    norm_num at hf
  · exact congrArg Prod.snd (e.injective hz)

/-- A switchable distinguished-block layout. These are finite structural
conditions, proved for the Wilson layout in the previous CDR paper. No lower
count or existence of a completion is a field of this structure. -/
structure CDRLatinBlockTemplate (J V : Type*) [DecidableEq V] (n : ℕ) (col : V → Fin 3) where
  chart : J → ((Fin 3 × Fin n) ↪ V)
  packing : (J → LatinArray n) → Finset (Finset V)
  card_three : ∀ Λ B, B ∈ packing Λ → B.card = 3
  pair_unique : ∀ Λ, pairPacking (packing Λ)
  bicoloured : ∀ Λ B, B ∈ packing Λ → (B.image col).card = 2
  footprint_eq : ∀ Λ M x y, x ≠ y →
    (pairFootprint (packing Λ) x y ↔ pairFootprint (packing M) x y)
  cell_mem : ∀ Λ j x y, chartLatinBlock (chart j) (Λ j) x y ∈ packing Λ

namespace CDRLatinBlockTemplate

variable {J V : Type*} [DecidableEq V] {n : ℕ} {col : V → Fin 3}
variable (T : CDRLatinBlockTemplate J V n col) (S : CDRBicolour.STS V)
variable (Λ₀ : J → LatinArray n) (hbase : T.packing Λ₀ ⊆ S.blocks)

def completed (Λ : J → LatinArray n) : CDRBicolour.STS V :=
  replaceSteinerPacking S (T.packing Λ₀) (T.packing Λ) hbase
    (T.card_three Λ) (T.pair_unique Λ) (T.footprint_eq Λ Λ₀)

theorem completed_base_blocks : (T.completed S Λ₀ hbase Λ₀).blocks = S.blocks :=
  sdiff_union_of_subset hbase

theorem residual_subset_completed (Λ : J → LatinArray n) :
    S.blocks \ T.packing Λ₀ ⊆ (T.completed S Λ₀ hbase Λ).blocks := subset_union_left

include hbase in
theorem residual_disjoint_packing (Λ : J → LatinArray n) :
    Disjoint (S.blocks \ T.packing Λ₀) (T.packing Λ) := by
  apply disjoint_left.mpr
  intro B hB hP
  obtain ⟨x,y,z,hxy,-,-,hxyz⟩ := card_eq_three.mp (T.card_three Λ B hP)
  have hx : x ∈ B := by rw [hxyz]; simp
  have hy : y ∈ B := by rw [hxyz]; simp
  obtain ⟨C,hC,hxC,hyC⟩ := (T.footprint_eq Λ Λ₀ x y hxy).mp ⟨B,hP,hx,hy⟩
  have he : B = C := (S.existsUnique_block x y hxy).unique
    ⟨(mem_sdiff.mp hB).1,hx,hy⟩ ⟨hbase hC,hxC,hyC⟩
  exact (mem_sdiff.mp hB).2 (he.symm ▸ hC)

/-- Arbitrary additive block tests split into a fixed residual contribution
and a local contribution. In particular, fixed residual configurations survive. -/
theorem completed_test_sum (Λ : J → LatinArray n) (w : Finset V → ℝ) :
    (∑ B ∈ (T.completed S Λ₀ hbase Λ).blocks, w B) =
      (∑ B ∈ S.blocks \ T.packing Λ₀, w B) + ∑ B ∈ T.packing Λ, w B :=
  sum_union (T.residual_disjoint_packing S Λ₀ hbase Λ)

theorem completed_same_test_sum (Λ M : J → LatinArray n) (w : Finset V → ℝ)
    (hw : (∑ B ∈ T.packing Λ, w B) = ∑ B ∈ T.packing M, w B) :
    (∑ B ∈ (T.completed S Λ₀ hbase Λ).blocks, w B) =
      ∑ B ∈ (T.completed S Λ₀ hbase M).blocks, w B := by
  rw [T.completed_test_sum S Λ₀ hbase Λ,T.completed_test_sum S Λ₀ hbase M,hw]

theorem completed_bicoloured (hS : CDRBicolour.IsStrictBicolouring S col) (Λ : J → LatinArray n) :
    CDRBicolour.IsStrictBicolouring (T.completed S Λ₀ hbase Λ) col :=
  replaceSteinerPacking_bicoloured S col _ _ hbase (T.card_three Λ) (T.pair_unique Λ)
    (T.footprint_eq Λ Λ₀) hS (T.bicoloured Λ)

/-- No multiplicity loss: the fixed row-column pairs recover every local array. -/
theorem completed_blocks_injective :
    Function.Injective (fun Λ => (T.completed S Λ₀ hbase Λ).blocks) := by
  intro Λ M h
  change (T.completed S Λ₀ hbase Λ).blocks = (T.completed S Λ₀ hbase M).blocks at h
  funext j
  apply Subtype.ext
  funext x y
  have hr : T.chart j (0,x) ≠ T.chart j (1,y) := by
    intro he
    have hf := congrArg Prod.fst ((T.chart j).injective he)
    norm_num at hf
  have hL : chartLatinBlock (T.chart j) (Λ j) x y ∈ (T.completed S Λ₀ hbase Λ).blocks :=
    mem_union_right _ (T.cell_mem Λ j x y)
  have hM : chartLatinBlock (T.chart j) (M j) x y ∈ (T.completed S Λ₀ hbase Λ).blocks := by
    rw [h]
    exact mem_union_right _ (T.cell_mem M j x y)
  have he := ((T.completed S Λ₀ hbase Λ).existsUnique_block _ _ hr).unique
    ⟨hL,by simp [chartLatinBlock],by simp [chartLatinBlock]⟩
    ⟨hM,by simp [chartLatinBlock],by simp [chartLatinBlock]⟩
  exact chartLatinBlock_symbol_eq _ _ _ _ _ he

def restrictedRealizations [Fintype J] (A : J → Finset (LatinArray n)) : Finset (Finset (Finset V)) :=
  (Fintype.piFinset A).image fun Λ => (T.completed S Λ₀ hbase Λ).blocks

theorem card_restrictedRealizations [Fintype J] (A : J → Finset (LatinArray n)) :
    (T.restrictedRealizations S Λ₀ hbase A).card = ∏ j, (A j).card := by
  rw [restrictedRealizations,card_image_of_injective _ (T.completed_blocks_injective S Λ₀ hbase)]
  exact Fintype.card_piFinset A

theorem mem_restrictedRealizations [Fintype J] (A : J → Finset (LatinArray n))
    {B : Finset (Finset V)} (hB : B ∈ T.restrictedRealizations S Λ₀ hbase A) :
    ∃ Λ : J → LatinArray n, (∀ j, Λ j ∈ A j) ∧
      B = (T.completed S Λ₀ hbase Λ).blocks := by
  obtain ⟨Λ,hΛ,hB⟩ := mem_image.mp hB
  exact ⟨Λ,Fintype.mem_piFinset.mp hΛ,hB.symm⟩

end CDRLatinBlockTemplate
end LatinonEntropy

#print axioms LatinonEntropy.replaceSteinerPacking
#print axioms LatinonEntropy.replaceSteinerPacking_bicoloured
#print axioms LatinonEntropy.chartLatinBlock_symbol_eq
#print axioms LatinonEntropy.CDRLatinBlockTemplate.completed_bicoloured
#print axioms LatinonEntropy.CDRLatinBlockTemplate.completed_base_blocks
#print axioms LatinonEntropy.CDRLatinBlockTemplate.residual_subset_completed
#print axioms LatinonEntropy.CDRLatinBlockTemplate.residual_disjoint_packing
#print axioms LatinonEntropy.CDRLatinBlockTemplate.completed_test_sum
#print axioms LatinonEntropy.CDRLatinBlockTemplate.completed_same_test_sum
#print axioms LatinonEntropy.CDRLatinBlockTemplate.completed_blocks_injective
#print axioms LatinonEntropy.CDRLatinBlockTemplate.card_restrictedRealizations
#print axioms LatinonEntropy.CDRLatinBlockTemplate.mem_restrictedRealizations
