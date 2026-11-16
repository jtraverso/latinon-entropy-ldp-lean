module

public import WeightedLabelPairs
public import FiniteWeightedCovariance

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem productLabel_covariance_le {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (htotal : ∀ i, ∑ a, p i a = 1)
    (i j : I) (a : A) :
    finiteCovariance (productLabelWeight p) (labelHit i a) (labelHit j a) ≤
      if i = j then 1 else 0 := by
  change productLabelMean p (fun ell => labelHit i a ell*labelHit j a ell)-
    productLabelMean p (labelHit i a)*productLabelMean p (labelHit j a) ≤ _
  simp only [productLabelMean_hit_pair p htotal,productLabelMean_hit p htotal]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have h := label_probability_le_one p hp htotal i a
    nlinarith only [h,sq_nonneg (p i a)]
  · simp only [hij,ite_false,sub_self,le_refl]

theorem pairedCell_covariance_zero {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ j, ∑ b, q j b = 1)
    (xy uv : I × J) (a : A) (b : B) (hx : xy.1 ≠ uv.1) (hy : xy.2 ≠ uv.2) :
    finiteCovariance (pairedLabelWeight p q) (pairedCellHit xy a b) (pairedCellHit uv a b) = 0 := by
  change pairedLabelMean p q (fun omega => pairedCellHit xy a b omega*pairedCellHit uv a b omega)-
    pairedLabelMean p q (pairedCellHit xy a b)*pairedLabelMean p q (pairedCellHit uv a b) = 0
  simp only [pairedLabelMean_cell_pair p q hp hq,pairedLabelMean_cell p q hp hq,hx,hy,ite_false]
  ring

theorem pairedCell_covariance_le {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ j b, 0 ≤ q j b)
    (hpt : ∀ i, ∑ a, p i a = 1) (hqt : ∀ j, ∑ b, q j b = 1)
    (xy uv : I × J) (a : A) (b : B) :
    finiteCovariance (pairedLabelWeight p q) (pairedCellHit xy a b) (pairedCellHit uv a b) ≤
      (if xy.1 = uv.1 then 1 else 0)+(if xy.2 = uv.2 then 1 else 0) := by
  have hpair := pairedLabelMean_cell_pair_le_one p q hp hq hpt hqt xy uv a b
  have hprod : 0 ≤ pairedLabelMean p q (pairedCellHit xy a b)*
      pairedLabelMean p q (pairedCellHit uv a b) := by
    rw [pairedLabelMean_cell p q hpt hqt,pairedLabelMean_cell p q hpt hqt]
    exact mul_nonneg (mul_nonneg (hp xy.1 a) (hq xy.2 b)) (mul_nonneg (hp uv.1 a) (hq uv.2 b))
  have hOne : finiteCovariance (pairedLabelWeight p q)
      (pairedCellHit xy a b) (pairedCellHit uv a b) ≤ 1 := by
    change pairedLabelMean p q (fun omega => pairedCellHit xy a b omega*pairedCellHit uv a b omega)-
      pairedLabelMean p q (pairedCellHit xy a b)*pairedLabelMean p q (pairedCellHit uv a b) ≤ 1
    linarith only [hpair,hprod]
  by_cases hx : xy.1 = uv.1
  · simp only [hx,ite_true]
    have hd : (0 : ℝ) ≤ (if xy.2 = uv.2 then 1 else 0) := by split_ifs <;> norm_num
    linarith only [hOne,hd]
  · by_cases hy : xy.2 = uv.2
    · simpa only [hx,hy,ite_false,ite_true,zero_add] using hOne
    · simp only [hx,hy,ite_false,zero_add]
      exact (pairedCell_covariance_zero p q hpt hqt xy uv a b hx hy).le

end LatinonEntropy
