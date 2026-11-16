module

public import BoxCorrection

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

def rectMass (B : Fin n → Fin n → ℝ) (S T : Finset (Fin n)) : ℝ :=
  ∑ y ∈ S, ∑ z ∈ T, B y z

theorem sum_subset_le_total (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (S : Finset (Fin n)) :
    (∑ i ∈ S, f i) ≤ ∑ i, f i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hf i)

theorem rectMass_nonneg (B : Fin n → Fin n → ℝ) (hB : ∀ y z, 0 ≤ B y z)
    (S T : Finset (Fin n)) : 0 ≤ rectMass B S T := by
  exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ => hB y z

theorem rectMass_univ_left (B : Fin n → Fin n → ℝ) (mass : ℝ)
    (hc : ∀ z, ∑ y, B y z = mass) (T : Finset (Fin n)) :
    rectMass B univ T = mass * T.card := by
  unfold rectMass
  rw [Finset.sum_comm]
  simp only [hc, Finset.sum_const, nsmul_eq_mul]
  ring

theorem rectMass_univ_right (B : Fin n → Fin n → ℝ) (mass : ℝ)
    (hr : ∀ y, ∑ z, B y z = mass) (S : Finset (Fin n)) :
    rectMass B S univ = mass * S.card := by
  unfold rectMass
  simp only [hr, Finset.sum_const, nsmul_eq_mul]
  ring

theorem rectMass_le_rows (B : Fin n → Fin n → ℝ) (mass : ℝ)
    (hB : ∀ y z, 0 ≤ B y z) (hr : ∀ y, ∑ z, B y z = mass)
    (S T : Finset (Fin n)) : rectMass B S T ≤ mass * S.card := by
  calc
    rectMass B S T ≤ ∑ y ∈ S, ∑ z, B y z :=
      Finset.sum_le_sum fun y _ => sum_subset_le_total (B y) (hB y) T
    _ = mass * S.card := rectMass_univ_right B mass hr S

theorem rectMass_le_cols (B : Fin n → Fin n → ℝ) (mass : ℝ)
    (hB : ∀ y z, 0 ≤ B y z) (hc : ∀ z, ∑ y, B y z = mass)
    (S T : Finset (Fin n)) : rectMass B S T ≤ mass * T.card := by
  calc
    rectMass B S T = ∑ z ∈ T, ∑ y ∈ S, B y z := Finset.sum_comm
    _ ≤ ∑ z ∈ T, ∑ y, B y z :=
      Finset.sum_le_sum fun z _ => sum_subset_le_total (fun y => B y z) (fun y => hB y z) S
    _ = mass * T.card := by simp only [hc, Finset.sum_const, nsmul_eq_mul]; ring

theorem sum_indicator (S : Finset (Fin n)) (v : ℝ) :
    (∑ i : Fin n, if i ∈ S then v else 0) = v * S.card := by
  classical
  simp only [← Finset.sum_filter]
  have h : univ.filter (fun i => i ∈ S) = S := by ext i; simp
  rw [h]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem cut_numerical_contradiction
    (N s t e eps rho C : ℝ) (hN : 0 < N) (heps : 0 < eps)
    (hrho : 0 < rho) (hC : 0 < C) (hparam : 16 ≤ C * rho * eps)
    (hs : eps * N / 4 ≤ s) (ht : N / (4 * C) ≤ t)
    (hcut : rho * s * t - rho * eps * N ^ 2 / (64 * C) ≤ e)
    (hsat : C * e ≤ N * t) : False := by
  have htpos : 0 < t := lt_of_lt_of_le (div_pos hN (by positivity)) ht
  have ht' : N ≤ 4 * C * t := by
    nlinarith [(div_le_iff₀ (by positivity : 0 < 4 * C)).mp ht]
  have hpenalty : rho * eps * N ^ 2 / (64 * C) ≤ rho * eps * N * t / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * C)).mpr
    have hh := mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ rho * eps * N)
    nlinarith
  have hs' := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ rho * t)
  have hlow : 3 * rho * eps * N * t / 16 ≤ e := by nlinarith
  have hc' := mul_le_mul_of_nonneg_left hlow hC.le
  have hp := mul_le_mul_of_nonneg_right hparam (by positivity : 0 ≤ 3 * N * t)
  nlinarith [mul_pos hN htpos]

end LatinonEntropy
