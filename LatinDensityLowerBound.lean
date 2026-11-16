module

public import LatinTensorLowerBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- The entropy of the density constant on each of the n^3 grid boxes. -/
def latinGridDensityEntropy {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  -(∑ x, ∑ i, ∑ j, f x i j * Real.log (f x i j)) / (n : ℝ)^3

theorem scaled_density_total_mass {n : ℕ} (hn : 0 < n)
    (f : Fin n → Fin n → Fin n → ℝ)
    (hrow : ∀ x i, ∑ j, f x i j = (n : ℝ)) :
    (∑ x, ∑ i, ∑ j, f x i j / (n : ℝ)) = (n : ℝ)^2 := by
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hr : ∀ x i, (∑ j, f x i j / (n : ℝ)) = 1 := by
    intro x i
    rw [← sum_div,hrow,div_self hnR]
  simp only [hr,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  ring

/-- Scaling a unit-line profile by n gives the grid density entropy with
exactly the n^2 log n term. This is an equality, without an asymptotic error. -/
theorem scaled_density_entropy {n : ℕ} (hn : 0 < n)
    (f : Fin n → Fin n → Fin n → ℝ) (hf : ∀ x i j, 0 < f x i j)
    (hrow : ∀ x i, ∑ j, f x i j = (n : ℝ)) :
    -(∑ x, ∑ i, ∑ j, (f x i j / (n : ℝ)) *
      Real.log (f x i j / (n : ℝ))) =
      (n : ℝ)^2 * Real.log (n : ℝ) + (n : ℝ)^2 * latinGridDensityEntropy f := by
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hm : (∑ x, ∑ i, ∑ j, f x i j) / (n : ℝ) = (n : ℝ)^2 := by
    simpa only [sum_div] using scaled_density_total_mass hn f hrow
  have he : ∀ x i j, (f x i j / (n : ℝ)) * Real.log (f x i j / (n : ℝ)) =
      f x i j * Real.log (f x i j) / (n : ℝ) -
        (f x i j / (n : ℝ)) * Real.log (n : ℝ) := by
    intro x i j
    rw [Real.log_div (hf x i j).ne' hnR]
    ring
  simp_rw [he]
  simp only [sum_sub_distrib,← sum_div,← sum_mul]
  rw [hm]
  unfold latinGridDensityEntropy
  field_simp [hnR]
  ring

/-- The finite lower bound in density notation, with the entropy normalized
by the volume n^-3 of each box. All three density line sums are n. -/
theorem finite_latin_density_lower_bound (a b rho eta : ℝ) (ha : 0 < a)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : Fin n → Fin n → Fin n → ℝ,
      (∀ x i j, a ≤ f x i j ∧ f x i j ≤ b) →
      (∀ x i, ∑ j, f x i j = (n : ℝ)) →
      (∀ x j, ∑ i, f x i j = (n : ℝ)) →
      (∀ i j, ∑ x, f x i j = (n : ℝ)) →
      (latinTensorCutFamily (fun x i j => f x i j / (n : ℝ)) rho).Nonempty ∧
      Real.exp ((n : ℝ)^2 * (Real.log (n : ℝ) - 2 + latinGridDensityEntropy f - eta)) ≤
        (latinTensorCutFamily (fun x i j => f x i j / (n : ℝ)) rho).card := by
  obtain ⟨N,hN,hcount⟩ := finite_latin_tensor_lower_bound a b rho eta ha hrho heta
  refine ⟨N,hN,?_⟩
  intro n hn f hbounds hrow hcol htime
  have hnpos : 0 < n := hN.trans_le hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hb : ∀ x i j, a/(n : ℝ) ≤ f x i j/(n : ℝ) ∧
      f x i j/(n : ℝ) ≤ b/(n : ℝ) := by
    intro x i j
    exact ⟨(div_le_div_iff_of_pos_right hnR).mpr (hbounds x i j).1,
      (div_le_div_iff_of_pos_right hnR).mpr (hbounds x i j).2⟩
  have hr : ∀ x i, ∑ j, f x i j/(n : ℝ) = 1 := by
    intro x i
    rw [← sum_div,hrow,div_self hnR.ne']
  have hc : ∀ x j, ∑ i, f x i j/(n : ℝ) = 1 := by
    intro x j
    rw [← sum_div,hcol,div_self hnR.ne']
  have ht : ∀ i j, ∑ x, f x i j/(n : ℝ) = 1 := by
    intro i j
    rw [← sum_div,htime,div_self hnR.ne']
  obtain ⟨hne,hcard⟩ := hcount n hn (fun x i j => f x i j/(n : ℝ)) hb hr hc ht
  refine ⟨hne,?_⟩
  have he := scaled_density_entropy hnpos f (fun x i j => ha.trans_le (hbounds x i j).1) hrow
  have hexp : (n : ℝ)^2 * (Real.log (n : ℝ) - 2 + latinGridDensityEntropy f - eta) =
      -(∑ x, ∑ i, ∑ j, (f x i j/(n : ℝ)) * Real.log (f x i j/(n : ℝ))) -
        (2+eta)*(n : ℝ)^2 := by
    rw [he]
    ring
  rw [hexp]
  exact hcard

end LatinonEntropy

#print axioms LatinonEntropy.scaled_density_total_mass
#print axioms LatinonEntropy.scaled_density_entropy
#print axioms LatinonEntropy.finite_latin_density_lower_bound
#print axioms LatinonEntropy.finite_latin_tensor_lower_bound

example {n : ℕ} : LatinonEntropy.latinGridDensityEntropy
    (fun (_ _ _ : Fin n) => (1 : ℝ)) = 0 := by
  simp [LatinonEntropy.latinGridDensityEntropy]
