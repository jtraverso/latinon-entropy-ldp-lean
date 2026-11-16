module

public import PermanentCap
public import TiltNormalization
public import FiniteHoeffding
public import VdWTheorem

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

theorem doubly_stochastic_permanent_log_lower (hn : 0 < n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1) :
    0 < Q.permanent ∧ -(n : ℝ) ≤ Real.log Q.permanent := by
  have hDS : Q ∈ doublyStochastic ℝ (Fin n) :=
    mem_doublyStochastic_iff_sum.mpr ⟨hQ,hrow,hcol⟩
  have hv := STS.van_der_waerden n Q hDS
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hfR : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hb : (0 : ℝ) < (n.factorial : ℝ) / (n : ℝ)^n := div_pos hfR (pow_pos hnR n)
  refine ⟨hb.trans_le hv,?_⟩
  have hlog := Real.log_le_log hb hv
  rw [Real.log_div hfR.ne' (pow_pos hnR n).ne',Real.log_pow] at hlog
  have hf := Real.le_sum_log_nat n
  rw [Real.sum_log_eq_log_factorial] at hf
  linarith

def matrixPairing (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i j * g i j

def centeredPermanentMGF (Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ sigma, permanentLaw Q sigma *
    Real.exp (t * (permutationStatistic g sigma - matrixPairing Q g))

theorem centeredPermanentMGF_ratio (Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) (t : ℝ) :
    centeredPermanentMGF Q g t =
      Real.exp (-t*matrixPairing Q g) * ((tiltedMatrix Q g t).permanent / Q.permanent) := by
  unfold centeredPermanentMGF
  rw [← permanentLaw_mgf]
  simp only [mul_sub,Real.exp_sub,neg_mul,Real.exp_neg,div_eq_mul_inv,mul_sum]
  apply sum_congr rfl
  intro sigma _
  ring

/-- The finite permanental MGF estimate. The integer cap on the normalized
tilt makes the error completely explicit. All permanent inequalities used
here are proved in this project or ported from the user's Gurvits proof. -/
theorem permanental_log_mgf_le (hn : 0 < n) (m : ℕ) (c : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (hcap : ∀ i j, Q i j ≤ c / n) (hm : Real.exp 2 * c ≤ m)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) :
    Real.log (centeredPermanentMGF Q g t) ≤ (n : ℝ)*t^2/2 + permanentCapError m n := by
  have hbase := doubly_stochastic_permanent_log_lower hn Q hQ hrow hcol
  have hrho := tiltRowMass_pos Q hQ hrow g hg t ht
  have hprod : (0 : ℝ) < ∏ i, tiltRowMass Q g t i := prod_pos (fun i _ => hrho i)
  have htilt := tilted_permanent_pos Q hQ hbase.1 g t
  have hfactor := tilted_permanent_normalized Q hQ hrow g hg t ht
  have hnorm : 0 < (normalizedTilt Q g t).permanent := by
    rw [hfactor] at htilt
    exact (mul_pos_iff_of_pos_left hprod).mp htilt
  have hnormcap : ∀ i j, normalizedTilt Q g t i j ≤ (m : ℝ) / n := by
    intro i j
    calc
      _ ≤ Real.exp 2 * Q i j := normalizedTilt_entry_le Q hQ hrow g hg t ht i j
      _ ≤ Real.exp 2 * (c/n) := mul_le_mul_of_nonneg_left (hcap i j) (Real.exp_pos 2).le
      _ = (Real.exp 2*c)/n := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  have hup := log_permanent_cap hn m (normalizedTilt Q g t)
    (normalizedTilt_nonneg Q hQ hrow g hg t ht)
    (normalizedTilt_row Q hQ hrow g hg t ht) hnorm hnormcap
  have hlogfactor : Real.log (tiltedMatrix Q g t).permanent =
      (∑ i, Real.log (tiltRowMass Q g t i)) + Real.log (normalizedTilt Q g t).permanent := by
    rw [hfactor,Real.log_mul hprod.ne' hnorm.ne',Real.log_prod (fun i _ => (hrho i).ne')]
  have hrows : (∑ i, Real.log (tiltRowMass Q g t i)) ≤
      t*matrixPairing Q g + (n : ℝ)*t^2/2 := by
    have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      finite_log_mgf_le (Q i) (g i) (hQ i) (hrow i) (hg i) t (hrho i))
    simpa only [tiltRowMass,tiltedMatrix,matrixPairing,sum_add_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using h
  rw [centeredPermanentMGF_ratio,
    Real.log_mul (Real.exp_pos _).ne' (div_pos htilt hbase.1).ne',
    Real.log_exp,Real.log_div htilt.ne' hbase.1.ne',hlogfactor]
  linarith [hbase.2]

end LatinonEntropy

#print axioms LatinonEntropy.doubly_stochastic_permanent_log_lower
#print axioms LatinonEntropy.permanental_log_mgf_le
