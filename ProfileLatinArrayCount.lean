module

public import UniformProfileHistoryCount
public import HistoryLatinArray

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology
open scoped Classical

def profileAtomToLatinArray {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ)
    (h : {h // h ∈ profileLatinHistoryAtoms P eta}) : LatinArray n := by
  have hg := h.property
  simp only [profileLatinHistoryAtoms,goodHistoryAtoms,mem_filter,mem_univ,true_and] at hg
  exact historyToLatinArray h.val.val (histories_length h.val.property) hg.1

def profileLatinArrayFamily {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ) : Finset (LatinArray n) :=
  univ.image (profileAtomToLatinArray P eta)

theorem profileAtomToLatinArray_injective {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ) :
    Function.Injective (profileAtomToLatinArray P eta) := by
  intro h g he
  apply Subtype.ext
  apply Subtype.ext
  exact historyArray_injective h.val.val g.val.val
    (histories_length h.val.property) (histories_length g.val.property)
    (congrArg (fun L : LatinArray n => L.val) he)

theorem profile_latin_array_family_card {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ) :
    (profileLatinArrayFamily P eta).card = (profileLatinHistoryAtoms P eta).card := by
  rw [profileLatinArrayFamily,card_image_of_injective _ (profileAtomToLatinArray_injective P eta),
    card_univ,Fintype.card_coe]

theorem profile_latin_array_family_witness {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ)
    (L : LatinArray n) (hL : L ∈ profileLatinArrayFamily P eta) :
    ∃ (h : LatinHistory n) (hlen : h.length = n), LatinHistoryValid h ∧
      historyArray h hlen = L.val ∧ profileCutClose P h eta := by
  obtain ⟨h,_,he⟩ := mem_image.mp hL
  have hg := h.property
  simp only [profileLatinHistoryAtoms,goodHistoryAtoms,mem_filter,mem_univ,true_and] at hg
  exact ⟨h.val.val,histories_length h.val.property,hg.1,
    congrArg (fun L : LatinArray n => L.val) he,hg.2⟩

/-- These are distinct Latin arrays obtained from the cut-close full
histories, in chronological row order. The cardinality transfer is exact. -/
theorem eventually_uniform_profile_latin_array_count (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      profileEntropy P-2*(n : ℝ)^2-eta*(n : ℝ)^2 ≤
        Real.log ((profileLatinArrayFamily P (4*eps)).card : ℝ) := by
  filter_upwards [eventually_uniform_profile_history_count a b eps ha heps heps1 eta heta]
    with n hn
  intro P hPa hPb
  rw [profile_latin_array_family_card]
  exact hn P hPa hPb

end LatinonEntropy

#print axioms LatinonEntropy.profile_latin_array_family_card
#print axioms LatinonEntropy.eventually_uniform_profile_latin_array_count
