module

public import CDRLatinBlockTransfer
public import SeriesCDR.WilsonCross

@[expose] public section

/-! Instantiation of the replacement theorem by the actual Wilson cross-block
construction from the CDR paper. Its finite packing proofs are retained in
SeriesCDR.WilsonCross; none of the structural template fields is postulated. -/

noncomputable section

namespace LatinonEntropy

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption
open CDRBicolour.Absorption.Count.Wilson
open scoped Classical

variable {a b c g n : ℕ} {G : Finset (Finset (Fin g))}

/-- The source cut uses the current array type, definitionally equal to
the original CDR Latin-square subtype. No conversion hypothesis is needed. -/
theorem wilson_latin_array_representation (G : Finset (Finset (Fin g))) (n : ℕ) :
    LFam G n = (Ix G → {l : Fin n → Fin n → Fin n // STS.IsLatin l}) := rfl

def wilsonLatinChart (h : WCond a b c g n) (j : Ix G) :
    (Fin 3 × Fin n) ↪ Fin (a+b+c) where
  toFun p := gv h (grp3 j.1.val p.1) (![j.2.1,j.2.2,tau j.2.1 j.2.2] p.1) p.2
  inj' := by
    intro p q he
    obtain ⟨hk,-,hi⟩ := gv_inj h he
    have hpq := grp3_inj (mem_OT.mp j.1.property).1 (mem_OT.mp j.1.property).2.1 hk
    exact Prod.ext hpq hi

theorem wilsonLatinChart_block (h : WCond a b c g n) (Λ : Ix G → LatinArray n)
    (j : Ix G) (x y : Fin n) :
    chartLatinBlock (wilsonLatinChart h j) (Λ j) x y = blk h Λ (j,x,y) := rfl

theorem wilson_pairFootprint_iff (h : WCond a b c g n) (Λ : Ix G → LatinArray n)
    {x y : Fin (a+b+c)} (hxy : x ≠ y) :
    pairFootprint (crossP h Λ) x y ↔ s(x,y) ∈ (crossP h Λ).biUnion triEdges := by
  constructor
  · rintro ⟨B,hB,hx,hy⟩
    exact mem_biUnion.mpr ⟨B,hB,mem_tE.mpr ⟨hx,hy,hxy⟩⟩
  · intro he
    obtain ⟨B,hB,hxyB⟩ := mem_biUnion.mp he
    exact ⟨B,hB,(mem_tE.mp hxyB).1,(mem_tE.mp hxyB).2.1⟩

/-- The previous paper's concrete Wilson layout supplies every finite
condition of the distinguished Latin-block transfer. -/
def wilsonLatinBlockTemplate (h : WCond a b c g n) (hG : STS.IsSTS G) :
    CDRLatinBlockTemplate (Ix G) (Fin (a+b+c)) n (col3 a b c) where
  chart := wilsonLatinChart h
  packing := crossP h
  card_three Λ B hB := (crossP_allowed h Λ B hB).1
  pair_unique Λ := by
    intro B hB C hC x y hxy hxB hyB hxC hyC
    by_contra hne
    exact disjoint_left.mp (crossP_disj h hG Λ hB hC hne)
      (mem_tE.mpr ⟨hxB,hyB,hxy⟩) (mem_tE.mpr ⟨hxC,hyC,hxy⟩)
  bicoloured Λ B hB := by
    have hc := (crossP_allowed h Λ B hB).2.2.2
    change ((B.val.map (col3 a b c)).toFinset).card = 2 at hc
    rw [Multiset.toFinset_map,Finset.val_toFinset] at hc
    exact hc
  footprint_eq Λ M x y hxy := by
    rw [wilson_pairFootprint_iff h Λ hxy,wilson_pairFootprint_iff h M hxy,
      mem_crossEdges h hG Λ,mem_crossEdges h hG M]
  cell_mem Λ j x y := by
    rw [wilsonLatinChart_block]
    exact mem_image.mpr ⟨(j,x,y),mem_univ _,rfl⟩

theorem wilson_blk_injective (h : WCond a b c g n) (hG : STS.IsSTS G)
    (Λ : Ix G → LatinArray n) : Function.Injective (blk h Λ) := by
  intro x y he
  have m0 : pos h Λ x 0 ∈ blk h Λ y := by rw [← he]; exact (mem_blk h).mpr ⟨0,rfl⟩
  have m1 : pos h Λ x 1 ∈ blk h Λ y := by rw [← he]; exact (mem_blk h).mpr ⟨1,rfl⟩
  obtain ⟨l0,e0⟩ := (mem_blk h).mp m0
  obtain ⟨l1,e1⟩ := (mem_blk h).mp m1
  obtain ⟨ho,rfl,rfl⟩ := share_two h hG (by decide : (0 : Fin 3) ≠ 1) e0.symm e1.symm
  exact cell_eq_01 h ho e0.symm e1.symm

/-- Every colour-multiset test, including the six exact CDR block types,
has the same packing total for every choice of internal Latin squares. -/
theorem wilson_packing_colour_test_sum (h : WCond a b c g n) (hG : STS.IsSTS G)
    (Λ M : Ix G → LatinArray n) (w : Multiset (Fin 3) → ℝ) :
    (∑ B ∈ crossP h Λ, w (B.val.map (col3 a b c))) =
      ∑ B ∈ crossP h M, w (B.val.map (col3 a b c)) := by
  unfold crossP
  rw [sum_image (wilson_blk_injective h hG Λ).injOn,
    sum_image (wilson_blk_injective h hG M).injOn]
  apply sum_congr rfl
  intro x _
  congr 1
  unfold blk
  rw [val_map_triple (col3 a b c) (pos_ne h Λ x (by decide : (0 : Fin 3) ≠ 1))
      (pos_ne h Λ x (by decide : (2 : Fin 3) ≠ 0))
      (pos_ne h Λ x (by decide : (2 : Fin 3) ≠ 1)),
    val_map_triple (col3 a b c) (pos_ne h M x (by decide : (0 : Fin 3) ≠ 1))
      (pos_ne h M x (by decide : (2 : Fin 3) ≠ 0))
      (pos_ne h M x (by decide : (2 : Fin 3) ≠ 1))]
  simp only [col3_pos]

theorem wilson_completed_colour_test_sum (h : WCond a b c g n) (hG : STS.IsSTS G)
    (S : CDRBicolour.STS (Fin (a+b+c))) (Λ₀ : Ix G → LatinArray n)
    (hbase : crossP h Λ₀ ⊆ S.blocks) (Λ M : Ix G → LatinArray n)
    (w : Multiset (Fin 3) → ℝ) :
    (∑ B ∈ ((wilsonLatinBlockTemplate h hG).completed S Λ₀ hbase Λ).blocks,
      w (B.val.map (col3 a b c))) =
    ∑ B ∈ ((wilsonLatinBlockTemplate h hG).completed S Λ₀ hbase M).blocks,
      w (B.val.map (col3 a b c)) :=
  (wilsonLatinBlockTemplate h hG).completed_same_test_sum S Λ₀ hbase Λ M _
    (wilson_packing_colour_test_sum h hG Λ M w)

theorem wilson_completed_exact_type_count (h : WCond a b c g n) (hG : STS.IsSTS G)
    (S : CDRBicolour.STS (Fin (a+b+c))) (Λ₀ : Ix G → LatinArray n)
    (hbase : crossP h Λ₀ ⊆ S.blocks) (Λ M : Ix G → LatinArray n)
    (typ : Multiset (Fin 3)) :
    (((wilsonLatinBlockTemplate h hG).completed S Λ₀ hbase Λ).blocks.filter
      (fun B => B.val.map (col3 a b c) = typ)).card =
    (((wilsonLatinBlockTemplate h hG).completed S Λ₀ hbase M).blocks.filter
      (fun B => B.val.map (col3 a b c) = typ)).card := by
  have he := wilson_completed_colour_test_sum h hG S Λ₀ hbase Λ M
    (fun t => if t = typ then (1 : ℝ) else 0)
  simp only [sum_boole] at he
  exact_mod_cast he

theorem wilson_completed_exact_type_count_eq_base (h : WCond a b c g n) (hG : STS.IsSTS G)
    (S : CDRBicolour.STS (Fin (a+b+c))) (Λ₀ : Ix G → LatinArray n)
    (hbase : crossP h Λ₀ ⊆ S.blocks) (Λ : Ix G → LatinArray n)
    (typ : Multiset (Fin 3)) :
    (((wilsonLatinBlockTemplate h hG).completed S Λ₀ hbase Λ).blocks.filter
      (fun B => B.val.map (col3 a b c) = typ)).card =
    (S.blocks.filter (fun B => B.val.map (col3 a b c) = typ)).card := by
  have he := wilson_completed_exact_type_count h hG S Λ₀ hbase Λ Λ₀ typ
  rw [(wilsonLatinBlockTemplate h hG).completed_base_blocks S Λ₀ hbase] at he
  exact he

end LatinonEntropy

#print axioms LatinonEntropy.wilsonLatinChart_block
#print axioms LatinonEntropy.wilson_latin_array_representation
#print axioms LatinonEntropy.wilson_pairFootprint_iff
#print axioms LatinonEntropy.wilsonLatinBlockTemplate
#print axioms LatinonEntropy.wilson_blk_injective
#print axioms LatinonEntropy.wilson_packing_colour_test_sum
#print axioms LatinonEntropy.wilson_completed_colour_test_sum
#print axioms LatinonEntropy.wilson_completed_exact_type_count
#print axioms LatinonEntropy.wilson_completed_exact_type_count_eq_base
