module

public import SymbolFloorCuts
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def symbolIntervalClass (n : ℕ) (a b : ℝ) : Finset (Fin n) :=
  univ.filter (fun z => symbolFloorCut n a ≤ z.val ∧ z.val < symbolFloorCut n b)

def symbolFloorIndicator {n : ℕ} (z : Fin n) (a b : ℝ) : ℝ :=
  if z ∈ symbolIntervalClass n a b then 1 else 0

theorem symbolIntervalWeight_eq_indicator_off_boundary {n : ℕ} (hn : 0 < n) (z : Fin n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hza : z.val ≠ symbolFloorCut n a) (hzb : z.val ≠ symbolFloorCut n b) :
    symbolIntervalWeight z a b = symbolFloorIndicator z a b := by
  by_cases hz : symbolFloorCut n a ≤ z.val ∧ z.val < symbolFloorCut n b
  · have hlow : symbolFloorCut n a < z.val := by omega
    have hL := symbolGridLower_ge_of_cut_lt hn z a hlow
    have hU := symbolGridUpper_le_of_lt_cut hn z b hb hz.2
    rw [symbolIntervalWeight_eq_one hn z a b hL hU]
    simp only [symbolFloorIndicator,symbolIntervalClass,mem_filter,mem_univ,true_and,hz,ite_true]
  · have hzero : symbolIntervalWeight z a b = 0 := by
      by_cases hlow : z.val < symbolFloorCut n a
      · exact symbolIntervalWeight_eq_zero_left z a b (symbolGridUpper_le_of_lt_cut hn z a ha hlow)
      · have hhigh : symbolFloorCut n b < z.val := by omega
        exact symbolIntervalWeight_eq_zero_right z a b (symbolGridLower_ge_of_cut_lt hn z b hhigh)
    rw [hzero]
    simp only [symbolFloorIndicator,symbolIntervalClass,mem_filter,mem_univ,true_and,hz,ite_false]

theorem symbolFloorIndicator_nonneg {n : ℕ} (z : Fin n) (a b : ℝ) : 0 ≤ symbolFloorIndicator z a b := by
  unfold symbolFloorIndicator
  split_ifs <;> norm_num

theorem symbolFloorIndicator_le_one {n : ℕ} (z : Fin n) (a b : ℝ) : symbolFloorIndicator z a b ≤ 1 := by
  unfold symbolFloorIndicator
  split_ifs <;> norm_num

theorem symbolIntervalClass_card (n : ℕ) (a b : ℝ) (hb : b ≤ 1) :
    (symbolIntervalClass n a b).card = symbolFloorCut n b-symbolFloorCut n a := by
  have he : (symbolIntervalClass n a b).image Fin.val =
      Ico (symbolFloorCut n a) (symbolFloorCut n b) := by
    ext k
    simp only [mem_image,mem_Ico]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (mem_filter.mp hz).2
    · intro hk
      have hkn : k < n := hk.2.trans_le (symbolFloorCut_le_order n hb)
      refine ⟨⟨k,hkn⟩,?_,rfl⟩
      simp only [symbolIntervalClass,mem_filter,mem_univ,true_and]
      exact hk
  calc
    _ = ((symbolIntervalClass n a b).image Fin.val).card :=
      (card_image_of_injective _ Fin.val_injective).symm
    _ = _ := by rw [he,Nat.card_Ico]

theorem symbolIntervalClass_card_error (n : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((symbolIntervalClass n a b).card : ℝ)-(n : ℝ)*(b-a)| < 1 := by
  rw [symbolIntervalClass_card n a b hb,Nat.cast_sub (symbolFloorCut_mono n hab)]
  have hA := symbolFloorCut_le_mul n ha
  have hB := symbolFloorCut_le_mul n (ha.trans hab)
  have hA' := symbolFloorCut_mul_lt_add_one n a
  have hB' := symbolFloorCut_mul_lt_add_one n b
  apply abs_lt.mpr
  constructor <;> nlinarith only [hA,hB,hA',hB']

theorem symbolIntervalClass_proportion_error {n : ℕ} (hn : 0 < n) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((symbolIntervalClass n a b).card : ℝ)/(n : ℝ)-(b-a)| < 1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : ((symbolIntervalClass n a b).card : ℝ)/(n : ℝ)-(b-a) =
      (((symbolIntervalClass n a b).card : ℝ)-(n : ℝ)*(b-a))/(n : ℝ) := by
    field_simp [hnR.ne']
  rw [he,abs_div,abs_of_pos hnR]
  exact (div_lt_div_iff_of_pos_right hnR).mpr (symbolIntervalClass_card_error n a b ha hab hb)

theorem exists_symbolIntervalClass_size_threshold (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (M : ℝ)^2 ≤ ((symbolIntervalClass n a b).card : ℝ) := by
  have hlen : 0 < b-a := sub_pos.mpr hab
  obtain ⟨K,hK⟩ := exists_nat_gt (((M : ℝ)^2+1)/(b-a))
  refine ⟨max 1 K,by omega,?_⟩
  intro n hn
  have hKn : (K : ℝ) ≤ n := Nat.cast_le.mpr ((le_max_right _ _).trans hn)
  have hlarge : (M : ℝ)^2+1 < (n : ℝ)*(b-a) :=
    (div_lt_iff₀ hlen).mp (hK.trans_le hKn)
  have herr := (abs_lt.mp (symbolIntervalClass_card_error n a b ha hab.le hb)).1
  linarith only [hlarge,herr]

def symbolBoundaryIndicator {n : ℕ} (z : Fin n) (a : ℝ) : ℝ :=
  if z.val = symbolFloorCut n a then 1 else 0

theorem symbolIntervalWeight_indicator_error {n : ℕ} (hn : 0 < n) (z : Fin n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |symbolIntervalWeight z a b-symbolFloorIndicator z a b| ≤
      symbolBoundaryIndicator z a+symbolBoundaryIndicator z b := by
  have hunit : |symbolIntervalWeight z a b-symbolFloorIndicator z a b| ≤ 1 := by
    apply abs_le.mpr
    have hw0 := symbolIntervalWeight_nonneg z a b
    have hw1 := symbolIntervalWeight_le_one hn z a b
    have hi0 := symbolFloorIndicator_nonneg z a b
    have hi1 := symbolFloorIndicator_le_one z a b
    constructor <;> linarith only [hw0,hw1,hi0,hi1]
  have hbn : ∀ t : ℝ, 0 ≤ symbolBoundaryIndicator z t := by
    intro t
    unfold symbolBoundaryIndicator
    split_ifs <;> norm_num
  by_cases hza : z.val = symbolFloorCut n a
  · rw [show symbolBoundaryIndicator z a = 1 from ite_eq_left hza]
    linarith only [hunit,hbn b]
  · by_cases hzb : z.val = symbolFloorCut n b
    · rw [show symbolBoundaryIndicator z b = 1 from ite_eq_left hzb]
      linarith only [hunit,hbn a]
    · rw [symbolIntervalWeight_eq_indicator_off_boundary hn z a b ha hb hza hzb,
        sub_self,abs_zero,show symbolBoundaryIndicator z a = 0 from ite_eq_right hza,
        show symbolBoundaryIndicator z b = 0 from ite_eq_right hzb]
      norm_num

end LatinonEntropy

#print axioms LatinonEntropy.symbolIntervalWeight_eq_indicator_off_boundary
#print axioms LatinonEntropy.symbolIntervalClass_card
#print axioms LatinonEntropy.symbolIntervalClass_card_error
#print axioms LatinonEntropy.symbolIntervalClass_proportion_error
#print axioms LatinonEntropy.exists_symbolIntervalClass_size_threshold
#print axioms LatinonEntropy.symbolIntervalWeight_indicator_error
