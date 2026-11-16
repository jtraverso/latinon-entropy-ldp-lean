module

public import RectangleMass

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- The host hypotheses and a feasible matrix, in the scale B=nQ. -/
structure ScaledResidualData (n : ℕ) where
  eps : ℝ
  rho : ℝ
  ell : ℝ
  C : ℝ
  d : ℝ
  npos : 0 < (n : ℝ)
  eps_pos : 0 < eps
  rho_pos : 0 < rho
  rho_le : rho ≤ 1
  ell_nonneg : 0 ≤ ell
  ell_le : ell ≤ 1 / 4
  C_pos : 0 < C
  capacity : 16 ≤ C * rho * eps
  A : Fin n → Fin n → ℝ
  B : Fin n → Fin n → ℝ
  binary : ∀ y z : Fin n, A y z = 0 ∨ A y z = 1
  Arow : ∀ y : Fin n, (∑ z : Fin n, A y z) = d
  Acol : ∀ z : Fin n, (∑ y : Fin n, A y z) = d
  degree : eps * n ≤ d
  bounds : ∀ y z : Fin n, ell * A y z ≤ B y z ∧ B y z ≤ C * A y z
  Brow : ∀ y : Fin n, (∑ z : Fin n, B y z) = (n : ℝ)
  Bcol : ∀ z : Fin n, (∑ y : Fin n, B y z) = (n : ℝ)
  cut : ∀ S T : Finset (Fin n),
    rho * S.card * T.card - rho * eps * (n : ℝ)^2 / (64 * C) ≤ rectMass A S T

namespace ScaledResidualData

variable {n : ℕ} (H : ScaledResidualData n)

def forwardSet (y : Fin n) : Finset (Fin n) := univ.filter (fun z => H.B y z < H.C * H.A y z)
def backwardSet (y : Fin n) : Finset (Fin n) := univ.filter (fun z => H.ell * H.A y z < H.B y z)
def backwardExpand (T : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun y => ∃ z ∈ T, H.ell * H.A y z < H.B y z)
def forwardExpand (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun z => ∃ y ∈ S, H.B y z < H.C * H.A y z)
def missed (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun z => z ∉ H.forwardExpand S)

theorem A_nonneg (y z : Fin n) : 0 ≤ H.A y z := by
  rcases H.binary y z with h | h <;> simp [h]
theorem A_le_one (y z : Fin n) : H.A y z ≤ 1 := by
  rcases H.binary y z with h | h <;> simp [h]
theorem B_nonneg (y z : Fin n) : 0 ≤ H.B y z :=
  (mul_nonneg H.ell_nonneg (H.A_nonneg y z)).trans (H.bounds y z).1
theorem B_le_C (y z : Fin n) : H.B y z ≤ H.C :=
  (H.bounds y z).2.trans (by simpa using mul_le_mul_of_nonneg_left (H.A_le_one y z) H.C_pos.le)
theorem ellA_le (y z : Fin n) : H.ell * H.A y z ≤ H.ell := by
  simpa using mul_le_mul_of_nonneg_left (H.A_le_one y z) H.ell_nonneg

theorem Ceps_ge : 16 ≤ H.C * H.eps := by
  have h := mul_le_mul_of_nonneg_right H.rho_le (mul_nonneg H.C_pos.le H.eps_pos.le)
  nlinarith [H.capacity]

theorem forward_card (y : Fin n) : H.eps * n / 2 ≤ ((H.forwardSet y).card : ℝ) := by
  have hpoint : ∀ z, H.A y z ≤
      (if z ∈ H.forwardSet y then (1 : ℝ) else 0) + H.B y z / H.C := by
    intro z
    by_cases hz : z ∈ H.forwardSet y
    · simp only [ite_eq_left hz]
      have hdiv := div_nonneg (H.B_nonneg y z) H.C_pos.le
      linarith [H.A_le_one y z]
    · simp only [ite_eq_right hz, zero_add]
      have hge : H.C * H.A y z ≤ H.B y z := by
        exact le_of_not_gt (by simpa [forwardSet] using hz)
      exact (le_div_iff₀ H.C_pos).mpr (by nlinarith)
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (univ : Finset (Fin n))) => hpoint z)
  rw [H.Arow y, Finset.sum_add_distrib, sum_indicator] at hsum
  have hd : (∑ z, H.B y z / H.C) = (n : ℝ) / H.C := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, H.Brow]
  rw [hd] at hsum
  have hinv : 1 / H.C ≤ H.eps / 2 := (div_le_iff₀ H.C_pos).mpr (by nlinarith [H.Ceps_ge])
  have hmul := mul_le_mul_of_nonneg_left hinv H.npos.le
  simp only [div_eq_mul_inv] at hsum hmul
  nlinarith [H.degree]

theorem backward_expand_card (T : Finset (Fin n)) :
    (1 - H.ell) * T.card ≤ ((H.backwardExpand T).card : ℝ) := by
  have hpoint : ∀ y, (∑ z ∈ T, H.B y z) ≤
      (if y ∈ H.backwardExpand T then (n : ℝ) else 0) + H.ell * T.card := by
    intro y
    by_cases hy : y ∈ H.backwardExpand T
    · have hh := sum_subset_le_total (H.B y) (H.B_nonneg y) T
      rw [H.Brow y] at hh
      simp only [ite_eq_left hy]
      have hn : 0 ≤ H.ell * (T.card : ℝ) := mul_nonneg H.ell_nonneg (Nat.cast_nonneg _)
      linarith
    · simp only [ite_eq_right hy, zero_add]
      have hh : (∑ z ∈ T, H.B y z) ≤ ∑ _z ∈ T, H.ell := by
        apply Finset.sum_le_sum
        intro z hz
        have hnot : ¬H.ell * H.A y z < H.B y z := by
          intro h
          exact hy (by simp only [backwardExpand, mem_filter, mem_univ, true_and]; exact ⟨z,hz,h⟩)
        exact (le_of_not_gt hnot).trans (H.ellA_le y z)
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hh
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (univ : Finset (Fin n))) => hpoint y)
  have heq : (∑ y, ∑ z ∈ T, H.B y z) = (n : ℝ) * T.card :=
    rectMass_univ_left H.B n H.Bcol T
  rw [heq, Finset.sum_add_distrib, sum_indicator] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hsum
  have hh : (n : ℝ) * ((1-H.ell) * T.card) ≤ (n : ℝ) * (H.backwardExpand T).card := by
    nlinarith
  exact le_of_mul_le_mul_left hh H.npos

theorem backward_card (y : Fin n) :
    (n : ℝ) / (4 * H.C) ≤ ((H.backwardSet y).card : ℝ) := by
  have hpoint : ∀ z, H.B y z ≤
      (if z ∈ H.backwardSet y then H.C else 0) + H.ell := by
    intro z
    by_cases hz : z ∈ H.backwardSet y
    · simp only [ite_eq_left hz]
      linarith [H.B_le_C y z, H.ell_nonneg]
    · simp only [ite_eq_right hz, zero_add]
      have hnot : ¬H.ell * H.A y z < H.B y z := by simpa [backwardSet] using hz
      exact (le_of_not_gt hnot).trans (H.ellA_le y z)
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (univ : Finset (Fin n))) => hpoint z)
  rw [H.Brow y, Finset.sum_add_distrib, sum_indicator] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hsum
  have hell := mul_le_mul_of_nonneg_right H.ell_le H.npos.le
  apply (div_le_iff₀ (mul_pos (by norm_num) H.C_pos : 0 < 4 * H.C)).mpr
  nlinarith

theorem missed_card (S : Finset (Fin n)) (hs : H.eps * n / 4 ≤ (S.card : ℝ)) :
    ((H.missed S).card : ℝ) < (n : ℝ) / (4 * H.C) := by
  by_contra h
  have hsat : H.C * rectMass H.A S (H.missed S) ≤ rectMass H.B S (H.missed S) := by
    unfold rectMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hn : z ∉ H.forwardExpand S := (mem_filter.mp hz).2
    exact le_of_not_gt (fun he => hn (by
      simp only [forwardExpand, mem_filter, mem_univ, true_and]
      exact ⟨y,hy,he⟩))
  have hu := rectMass_le_cols H.B n (H.B_nonneg) H.Bcol S (H.missed S)
  exact cut_numerical_contradiction n S.card (H.missed S).card (rectMass H.A S (H.missed S))
    H.eps H.rho H.C H.npos H.eps_pos H.rho_pos H.C_pos H.capacity hs
    (le_of_not_gt h) (H.cut S (H.missed S)) (hsat.trans hu)

theorem column_backward (z : Fin n) : ∃ y, H.ell * H.A y z < H.B y z := by
  by_contra! h
  have hs : (∑ y, H.B y z) ≤ ∑ _y : Fin n, H.ell :=
    Finset.sum_le_sum fun y _ => (h y).trans (H.ellA_le y z)
  rw [H.Bcol z] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hs
  have hell := mul_le_mul_of_nonneg_right H.ell_le H.npos.le
  nlinarith [H.npos]

theorem column_forward (z : Fin n) : ∃ y, H.B y z < H.C * H.A y z := by
  by_contra! h
  have hs : (∑ y, H.C * H.A y z) ≤ ∑ y, H.B y z := Finset.sum_le_sum fun y _ => h y
  rw [← Finset.mul_sum, H.Acol z, H.Bcol z] at hs
  have hd := mul_le_mul_of_nonneg_left H.degree H.C_pos.le
  have hp := mul_le_mul_of_nonneg_right H.Ceps_ge H.npos.le
  nlinarith [H.npos]

theorem row_four_steps
    (c : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (y target : Fin n) :
    ∃ t, CostWalk (boxResidual (fun i j => H.ell * H.A i j)
      (fun i j => H.C * H.A i j) H.B) c (.inl y) (.inl target) t 4 := by
  let T0 := H.forwardSet y
  let S := H.backwardExpand T0
  have hT : H.eps * n / 2 ≤ (T0.card : ℝ) := H.forward_card y
  have hS0 : (1-H.ell) * T0.card ≤ (S.card : ℝ) := H.backward_expand_card T0
  have hell := mul_le_mul_of_nonneg_right H.ell_le (Nat.cast_nonneg T0.card : (0 : ℝ) ≤ T0.card)
  have hS : H.eps * n / 4 ≤ (S.card : ℝ) := by nlinarith [mul_pos H.eps_pos H.npos]
  have hmiss := H.missed_card S hS
  have hback := H.backward_card target
  have hinter : ∃ z, z ∈ H.backwardSet target ∧ z ∈ H.forwardExpand S := by
    by_contra! hn
    have hsub : H.backwardSet target ⊆ H.missed S := by
      intro z hz
      exact mem_filter.mpr ⟨mem_univ _, hn z hz⟩
    have hcard : ((H.backwardSet target).card : ℝ) ≤ (H.missed S).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    linarith
  obtain ⟨z1, hzback, hzreach⟩ := hinter
  obtain ⟨y1, hy1, he3⟩ := (mem_filter.mp hzreach).2
  obtain ⟨z0, hz0, he2⟩ := (mem_filter.mp hy1).2
  have he1 := (mem_filter.mp hz0).2
  have he4 := (mem_filter.mp hzback).2
  let R := boxResidual (fun i j => H.ell * H.A i j) (fun i j => H.C * H.A i j) H.B
  have e1 : R (.inl y) (.inr z0) := he1
  have e2 : R (.inr z0) (.inl y1) := he2
  have e3 : R (.inl y1) (.inr z1) := he3
  have e4 : R (.inr z1) (.inl target) := he4
  have p0 : CostWalk R c (.inl y) (.inl y) 0 0 := .nil
  exact ⟨_, (((p0.snoc e1).snoc e2).snoc e3).snoc e4⟩

theorem diameter_six
    (c : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (u v : Fin n ⊕ Fin n) :
    ∃ t k, CostWalk (boxResidual (fun i j => H.ell * H.A i j)
      (fun i j => H.C * H.A i j) H.B) c u v t k ∧ k ≤ 6 := by
  cases u with
  | inl y =>
      cases v with
      | inl target =>
          obtain ⟨t,p⟩ := H.row_four_steps c y target
          exact ⟨t,4,p,by decide⟩
      | inr z =>
          obtain ⟨target,he⟩ := H.column_forward z
          obtain ⟨t,p⟩ := H.row_four_steps c y target
          exact ⟨_,5,p.snoc he,by decide⟩
  | inr z =>
      obtain ⟨y,he⟩ := H.column_backward z
      let R := boxResidual (fun i j => H.ell * H.A i j) (fun i j => H.C * H.A i j) H.B
      have p0 : CostWalk R c (.inr z) (.inr z) 0 0 := .nil
      have heR : R (.inr z) (.inl y) := he
      cases v with
      | inl target =>
          obtain ⟨t,p⟩ := H.row_four_steps c y target
          exact ⟨_,5,(p0.snoc heR).append p,by decide⟩
      | inr z' =>
          obtain ⟨target,he'⟩ := H.column_forward z'
          obtain ⟨t,p⟩ := H.row_four_steps c y target
          exact ⟨_,6,((p0.snoc heR).append p).snoc he',by decide⟩

end ScaledResidualData
end LatinonEntropy

#print axioms LatinonEntropy.ScaledResidualData.diameter_six
