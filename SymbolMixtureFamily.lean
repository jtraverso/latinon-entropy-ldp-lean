module

public import SymbolBlockEvaluation
public import UniformPushforward
public import FiniteEntropyCap

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def symbolMixtureInput {n q : ℕ} (color : Fin n → Fin q) (S : Finset (LatinArray n)) :
    Finset (symbolBlockStabilizer color × LatinArray n) := univ ×ˢ S

def symbolMixtureMap {n q : ℕ} (color : Fin n → Fin q)
    (p : symbolBlockStabilizer color × LatinArray n) : LatinArray n := symbolRelabelEquiv p.1.val p.2

def symbolMixtureFamily {n q : ℕ} (color : Fin n → Fin q) (S : Finset (LatinArray n)) :
    Finset (LatinArray n) := (symbolMixtureInput color S).image (symbolMixtureMap color)

def symbolMixtureWeight {n q : ℕ} (color : Fin n → Fin q) (S : Finset (LatinArray n))
    (L : LatinArray n) : ℝ := uniformImageWeight (symbolMixtureInput color S) (symbolMixtureMap color) L

theorem symbolMixtureInput_card {n q : ℕ} (color : Fin n → Fin q) (S : Finset (LatinArray n)) :
    (symbolMixtureInput color S).card = Fintype.card (symbolBlockStabilizer color)*S.card := by
  simp only [symbolMixtureInput,card_product,card_univ]

theorem symbolMixtureInput_nonempty {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) : (symbolMixtureInput color S).Nonempty := by
  obtain ⟨L,hL⟩ := hS
  exact ⟨(1,L),mem_product.mpr ⟨mem_univ _,hL⟩⟩

theorem symbolMixtureFamily_nonempty {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) : (symbolMixtureFamily color S).Nonempty := by
  obtain ⟨p,hp⟩ := symbolMixtureInput_nonempty color S hS
  exact ⟨symbolMixtureMap color p,mem_image.mpr ⟨p,hp,rfl⟩⟩

theorem symbolMixtureWeight_pos {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) (L : LatinArray n)
    (hL : L ∈ symbolMixtureFamily color S) : 0 < symbolMixtureWeight color S L :=
  uniformImageWeight_pos _ (symbolMixtureInput_nonempty color S hS) _ L hL

theorem symbolMixtureWeight_total {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) :
    (∑ L ∈ symbolMixtureFamily color S, symbolMixtureWeight color S L) = 1 :=
  uniformImageWeight_total _ (symbolMixtureInput_nonempty color S hS) _

theorem symbolMixtureWeight_le {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) (L : LatinArray n) :
    symbolMixtureWeight color S L ≤ 1/(S.card : ℝ) := by
  let : Nonempty (symbolBlockStabilizer color) := ⟨1⟩
  let B := finiteImageFiber (symbolMixtureInput color S) (symbolMixtureMap color) L
  have hi : Function.Injective (fun p : B => p.val.1) := by
    intro p r he
    change p.val.1 = r.val.1 at he
    apply Subtype.ext
    apply Prod.ext he
    have hp := p.property
    have hr := r.property
    simp only [B,finiteImageFiber,mem_filter] at hp hr
    have hpe : symbolRelabelEquiv p.val.1.val p.val.2 = L := hp.2
    have hre : symbolRelabelEquiv r.val.1.val r.val.2 = L := hr.2
    have hb := hpe.trans hre.symm
    rw [← he] at hb
    exact (symbolRelabelEquiv p.val.1.val).injective hb
  have hcard : B.card ≤ Fintype.card (symbolBlockStabilizer color) := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective (fun p : B => p.val.1) hi
  have hcardR : (B.card : ℝ) ≤ (Fintype.card (symbolBlockStabilizer color) : ℝ) := Nat.cast_le.mpr hcard
  have hG : (0 : ℝ) < Fintype.card (symbolBlockStabilizer color) := Nat.cast_pos.mpr Fintype.card_pos
  have hN : (0 : ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hden : ((symbolMixtureInput color S).card : ℝ) =
      (Fintype.card (symbolBlockStabilizer color) : ℝ)*(S.card : ℝ) := by
    rw [symbolMixtureInput_card,Nat.cast_mul]
  change (B.card : ℝ)/((symbolMixtureInput color S).card : ℝ) ≤ 1/(S.card : ℝ)
  rw [hden]
  calc
    _ ≤ (Fintype.card (symbolBlockStabilizer color) : ℝ)/
        ((Fintype.card (symbolBlockStabilizer color) : ℝ)*(S.card : ℝ)) :=
      div_le_div_of_nonneg_right hcardR (mul_pos hG hN).le
    _ = _ := by field_simp [hG.ne',hN.ne']

theorem symbol_mixture_entropy_lower {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) :
    Real.log (S.card : ℝ) ≤ weightedFamilyEntropy (symbolMixtureFamily color S) (symbolMixtureWeight color S) :=
  weighted_entropy_lower_of_point_cap _ _ (symbolMixtureWeight_pos color S hS)
    (symbolMixtureWeight_total color S hS) (S.card : ℝ)
    (Nat.cast_pos.mpr (card_pos.mpr hS)) (fun L _ => symbolMixtureWeight_le color S hS L)

end LatinonEntropy

#print axioms LatinonEntropy.symbolMixtureWeight_total
#print axioms LatinonEntropy.symbolMixtureWeight_le
#print axioms LatinonEntropy.symbol_mixture_entropy_lower
