module

public import WeightedLabelPairs

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem pairedLabelMean_fst {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (hq : ∀ j, ∑ b, q j b = 1)
    (F : (I → A) → ℝ) :
    pairedLabelMean p q (fun omega => F omega.1) = productLabelMean p F := by
  calc
    _ = pairedLabelMean p q (fun omega => F omega.1*1) := by
      apply finiteExpectation_congr
      intro omega
      exact (mul_one _).symm
    _ = productLabelMean p F*productLabelMean q (fun _ => 1) := pairedLabelMean_separable p q F (fun _ => 1)
    _ = _ := by rw [productLabelMean_const q hq 1,mul_one]

theorem pairedLabelMean_snd {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (hp : ∀ i, ∑ a, p i a = 1)
    (G : (J → B) → ℝ) :
    pairedLabelMean p q (fun omega => G omega.2) = productLabelMean q G := by
  calc
    _ = pairedLabelMean p q (fun omega => 1*G omega.2) := by
      apply finiteExpectation_congr
      intro omega
      exact (one_mul _).symm
    _ = productLabelMean p (fun _ => 1)*productLabelMean q G := pairedLabelMean_separable p q (fun _ => 1) G
    _ = _ := by rw [productLabelMean_const p hp 1,one_mul]

end LatinonEntropy
