module

public import ExpectedMainRowEntropy
public import ExpectedTailEntropy
public import ProfileEntropyError

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem expected_row_entropy_uniform_lower {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (t : ℕ) (ht : t < n) :
    profileFluidRowEntropy P t-(n : ℝ)-profileRowEntropyError P a b eps heps m-
      (if t = mainRange eps n then (n : ℝ)*Real.log (n : ℝ) else 0) ≤
      historyExpectation
        ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) t
        (kernelEntropy ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos)) := by
  let v := fixedCutDensity a b eps*(n : ℝ)^2/4
  have herr := profileRowEntropyError_nonneg P a b eps heps ha hb m
  rcases lt_trichotomy t (mainRange eps n) with hmain | hboundary | htail
  · have hrow := expected_main_row_entropy_lower P a b eps heps ha hb m hm hsize
      (mainRange eps n) (mainRange_degree eps heps1 n) t hmain
    have htn : (t : ℝ) ≤ n := Nat.cast_le.mpr ht.le
    have hscale := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htn
        (add_nonneg (Real.sqrt_nonneg (2*(n : ℝ)*permanentCapError m n)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
          (profileStabilityBound_nonneg P eps heps m))))
      (profileEntropyWeightCap_nonneg P eps heps)
    simp only [ne_of_lt hmain,ite_false,sub_zero]
    unfold profileRowEntropyError
    linarith only [hrow,hscale]
  · have hrow := expected_boundary_row_entropy_lower P eps heps v t ht
    simp only [hboundary,ite_true] at hrow ⊢
    linarith only [hrow,herr,Nat.cast_nonneg (α := ℝ) n]
  · have hrow := expected_tail_row_entropy_lower P eps heps v t ht htail
    simp only [ne_of_gt htail,ite_false,sub_zero]
    linarith only [hrow,herr]

/-- The full constructed law, including early stopped histories, the single
boundary row, and its actual regular fallback tail. -/
theorem profile_history_entropy_lower {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    profileEntropy P-2*(n : ℝ)^2-(n : ℝ)*profileRowEntropyError P a b eps heps m-
      (n : ℝ)*Real.log (n : ℝ) ≤
      historyEntropy
        ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) n := by
  let K := (profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos
  let E := profileRowEntropyError P a b eps heps m
  have hrows := sum_le_sum (fun t (ht : t ∈ range n) =>
    expected_row_entropy_uniform_lower P a b eps heps heps1 ha hb m hm hsize t (mem_range.mp ht))
  have hboundary : (∑ t ∈ range n,
      if t = mainRange eps n then (n : ℝ)*Real.log (n : ℝ) else 0) ≤
      (n : ℝ)*Real.log (n : ℝ) := by
    simp only [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n)
  have hfluid := profile_fluid_entropy_lower P
  have he : profileFluidEntropy P = ∑ t ∈ range n, profileFluidRowEntropy P t := by
    rw [profile_fluid_entropy_eq_sum_rows,Fin.sum_univ_eq_sum_range]
  rw [history_entropy_chain]
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] at hrows
  rw [he] at hfluid
  nlinarith only [hrows,hboundary,hfluid]

end LatinonEntropy

#print axioms LatinonEntropy.expected_row_entropy_uniform_lower
#print axioms LatinonEntropy.profile_history_entropy_lower
