module

public import ResidualDiameter

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

namespace CostWalk

theorem mono_relation {V : Type*} {R S : V → V → Prop} {c : V → V → ℝ}
    {u v : V} {t : ℝ} {k : ℕ} (p : CostWalk R c u v t k)
    (h : ∀ a b, R a b → S a b) : CostWalk S c u v t k := by
  induction p with
  | nil => exact .nil
  | snoc p edge ih => exact ih.snoc (h _ _ edge)

end CostWalk

theorem scale_entry_bound (N v a : ℝ) (hN : 0 < N) :
    N * (v / N * a) = v * a := by
  calc
    N * (v / N * a) = (v / N * N) * a := by ring
    _ = v * a := by rw [div_mul_cancel₀ _ hN.ne']

/-- Complete correction theorem from regularity and the stated cut bound.
There is no residual-diameter, optimizer, or potential hypothesis. -/
theorem quasirandom_box_correction
    {n : ℕ} (hn : 0 < n) (eps rho ell C d : ℝ)
    (heps : 0 < eps) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1/4) (hC : 0 < C)
    (hcapacity : 16 ≤ C * rho * eps)
    (A M : Fin n → Fin n → ℝ)
    (hA : ∀ y z, A y z = 0 ∨ A y z = 1)
    (hrowA : ∀ y, (∑ z, A y z) = d) (hcolA : ∀ z, (∑ y, A y z) = d)
    (hdegree : eps * n ≤ d)
    (hcut : ∀ S T : Finset (Fin n),
      rho * S.card * T.card - rho * eps * (n : ℝ)^2 / (64*C) ≤ rectMass A S T)
    (hM : ∀ y z, ell / n * A y z ≤ M y z ∧ M y z ≤ C / n * A y z) :
    ∃ Q : Fin n → Fin n → ℝ,
      (∀ y z, ell / n * A y z ≤ Q y z ∧ Q y z ≤ C / n * A y z) ∧
      (∀ y, ∑ z, Q y z = 1) ∧ (∀ z, ∑ y, Q y z = 1) ∧
      (∑ y, ∑ z, |Q y z - M y z|) ≤
        3 * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hAnonneg : ∀ y z, 0 ≤ A y z := by
    intro y z; rcases hA y z with h | h <;> simp [h]
  have hAone : ∀ y z, A y z ≤ 1 := by
    intro y z; rcases hA y z with h | h <;> simp [h]
  have hd : 0 < d := lt_of_lt_of_le (mul_pos heps hN) hdegree
  have hdN : d ≤ (n : ℝ) := by
    let y0 : Fin n := ⟨0,hn⟩
    calc
      d = ∑ z, A y0 z := (hrowA y0).symm
      _ ≤ ∑ _z : Fin n, (1 : ℝ) := Finset.sum_le_sum fun z _ => hAone y0 z
      _ = n := by simp
  have hCeps : 16 ≤ C * eps := by
    have h := mul_le_mul_of_nonneg_right hrho1 (mul_nonneg hC.le heps.le)
    nlinarith
  have hlo : ell / n ≤ 1 / d := by
    apply (div_le_div_iff₀ hN hd).mpr
    have hh := mul_le_mul_of_nonneg_right (show ell ≤ 1 by linarith) hd.le
    nlinarith
  have hhi : 1 / d ≤ C / n := by
    apply (div_le_div_iff₀ hd hN).mpr
    have h1 := mul_le_mul_of_nonneg_left hdegree hC.le
    have h2 := mul_le_mul_of_nonneg_right hCeps hN.le
    nlinarith
  let lower : Fin n → Fin n → ℝ := fun y z => ell / n * A y z
  let upper : Fin n → Fin n → ℝ := fun y z => C / n * A y z
  let Q0 : Fin n → Fin n → ℝ := fun y z => A y z / d
  have hQ0box : Q0 ∈ Set.Icc lower upper := by
    constructor
    · intro y z
      have h := mul_le_mul_of_nonneg_right hlo (hAnonneg y z)
      simpa [lower, Q0, div_eq_mul_inv, mul_comm] using h
    · intro y z
      have h := mul_le_mul_of_nonneg_right hhi (hAnonneg y z)
      simpa [upper, Q0, div_eq_mul_inv, mul_comm] using h
  have hQ0row : ∀ y, ∑ z, Q0 y z = 1 := by
    intro y
    simp only [Q0, div_eq_mul_inv, ← Finset.sum_mul, hrowA]
    exact mul_inv_cancel₀ hd.ne'
  have hQ0col : ∀ z, ∑ y, Q0 y z = 1 := by
    intro z
    simp only [Q0, div_eq_mul_inv, ← Finset.sum_mul, hcolA]
    exact mul_inv_cancel₀ hd.ne'
  have hMbox : M ∈ Set.Icc lower upper := ⟨fun y z => (hM y z).1, fun y z => (hM y z).2⟩
  have hdiam : ∀ Q : Fin n → Fin n → ℝ, Q ∈ Set.Icc lower upper →
      (∀ y, ∑ z, Q y z = 1) → (∀ z, ∑ y, Q y z = 1) →
      ∀ u v, ∃ t k, CostWalk (boxResidual lower upper Q) (boxResidualCost M Q) u v t k ∧ k ≤ 6 := by
    intro Q hbox hrows hcols u v
    let B : Fin n → Fin n → ℝ := fun y z => (n : ℝ) * Q y z
    have hbounds : ∀ y z, ell * A y z ≤ B y z ∧ B y z ≤ C * A y z := by
      intro y z
      have hl := mul_le_mul_of_nonneg_left (hbox.1 y z) hN.le
      have hu := mul_le_mul_of_nonneg_left (hbox.2 y z) hN.le
      change (n : ℝ) * (ell / n * A y z) ≤ (n : ℝ) * Q y z at hl
      change (n : ℝ) * Q y z ≤ (n : ℝ) * (C / n * A y z) at hu
      rw [scale_entry_bound _ _ _ hN] at hl hu
      exact ⟨hl,hu⟩
    have hBrows : ∀ y, (∑ z, B y z) = (n : ℝ) := by
      intro y
      simp only [B, ← Finset.mul_sum, hrows, mul_one]
    have hBcols : ∀ z, (∑ y, B y z) = (n : ℝ) := by
      intro z
      simp only [B, ← Finset.mul_sum, hcols, mul_one]
    let H : ScaledResidualData n := {
      eps := eps, rho := rho, ell := ell, C := C, d := d,
      npos := hN, eps_pos := heps, rho_pos := hrho, rho_le := hrho1,
      ell_nonneg := hell, ell_le := hell1, C_pos := hC, capacity := hcapacity,
      A := A, B := B, binary := hA, Arow := hrowA, Acol := hcolA,
      degree := hdegree, bounds := hbounds, Brow := hBrows, Bcol := hBcols, cut := hcut }
    obtain ⟨t,k,p,hk⟩ := H.diameter_six (boxResidualCost M Q) u v
    refine ⟨t,k,p.mono_relation ?_,hk⟩
    intro a b he
    cases a with
    | inl y =>
        cases b with
        | inl y' => exact False.elim he
        | inr z =>
            change (n : ℝ) * Q y z < C * A y z at he
            change Q y z < C / n * A y z
            apply lt_of_mul_lt_mul_left (a := (n : ℝ)) ?_ hN.le
            rw [scale_entry_bound _ _ _ hN]
            exact he
    | inr z =>
        cases b with
        | inr z' => exact False.elim he
        | inl y =>
            change ell * A y z < (n : ℝ) * Q y z at he
            change ell / n * A y z < Q y z
            apply lt_of_mul_lt_mul_left (a := (n : ℝ)) ?_ hN.le
            rw [scale_entry_bound _ _ _ hN]
            exact he
  obtain ⟨Q, hbox, hrow, hcol, hcost⟩ :=
    exists_box_correction_of_residual_diameter M lower upper Q0 hMbox hQ0box hQ0row hQ0col hdiam
  exact ⟨Q, fun y z => ⟨hbox.1 y z,hbox.2 y z⟩, hrow, hcol, hcost⟩

/-! The handoff's parameters, now with explicit entry bounds. -/

theorem correction_lemma
    {n : ℕ} (hn : 0 < n) (eps rho a c d : ℝ)
    (heps : 0 < eps) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (ha : 0 < a) (hac : a ≤ c)
    (A M : Fin n → Fin n → ℝ)
    (hA : ∀ y z, A y z = 0 ∨ A y z = 1)
    (hrowA : ∀ y, (∑ z, A y z) = d) (hcolA : ∀ z, (∑ y, A y z) = d)
    (hdegree : eps * n ≤ d)
    (hcut : ∀ S T : Finset (Fin n),
      rho * S.card * T.card - rho * eps * (n : ℝ)^2 /
        (64 * max c (16 / (rho * eps))) ≤ rectMass A S T)
    (hzero : ∀ y z, A y z = 0 → M y z = 0)
    (hM : ∀ y z, A y z = 1 → a / n ≤ M y z ∧ M y z ≤ c / n) :
    ∃ Q : Fin n → Fin n → ℝ,
      (∀ y, ∑ z, Q y z = 1) ∧ (∀ z, ∑ y, Q y z = 1) ∧
      (∀ y z, 0 ≤ Q y z) ∧
      (∀ y z, A y z = 0 → Q y z = 0) ∧
      (∀ y z, A y z = 1 → min (a/2) (1/4) / n ≤ Q y z ∧
        Q y z ≤ max c (16 / (rho * eps)) / n) ∧
      (∑ y, ∑ z, |Q y z - M y z|) ≤
        3 * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  let ell : ℝ := min (a/2) (1/4)
  let C : ℝ := max c (16 / (rho * eps))
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hell : 0 < ell := lt_min (half_pos ha) (by norm_num)
  have hell1 : ell ≤ 1/4 := min_le_right _ _
  have hella : ell ≤ a := (min_le_left _ _).trans (by linarith)
  have hcC : c ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le (lt_of_lt_of_le ha hac) hcC
  have hcapacity : 16 ≤ C * rho * eps := by
    have hh : 16 / (rho * eps) ≤ C := le_max_right _ _
    have hh' := (div_le_iff₀ (mul_pos hrho heps)).mp hh
    nlinarith
  have hMbox : ∀ y z, ell / n * A y z ≤ M y z ∧ M y z ≤ C / n * A y z := by
    intro y z
    rcases hA y z with hz | ho
    · simp [hz, hzero y z hz]
    · obtain ⟨hl, hu⟩ := hM y z ho
      have hl' := (div_le_div_of_nonneg_right hella hN.le).trans hl
      have hu' := hu.trans (div_le_div_of_nonneg_right hcC hN.le)
      simpa [ho] using And.intro hl' hu'
  obtain ⟨Q, hbox, hrow, hcol, hcost⟩ := quasirandom_box_correction hn eps rho ell C d
    heps hrho hrho1 hell.le hell1 hC hcapacity A M hA hrowA hcolA hdegree hcut hMbox
  have hoff : ∀ y z, A y z = 0 → Q y z = 0 := by
    intro y z hz
    have hh := hbox y z
    simp only [hz, mul_zero] at hh
    exact le_antisymm hh.2 hh.1
  have hon : ∀ y z, A y z = 1 → ell / n ≤ Q y z ∧ Q y z ≤ C / n := by
    intro y z hz
    simpa only [hz, mul_one] using hbox y z
  have hnonneg : ∀ y z, 0 ≤ Q y z := by
    intro y z
    rcases hA y z with hz | ho
    · rw [hoff y z hz]
    · exact (div_nonneg hell.le hN.le).trans (hon y z ho).1
  exact ⟨Q,hrow,hcol,hnonneg,hoff,hon,hcost⟩

end LatinonEntropy

#print axioms LatinonEntropy.quasirandom_box_correction
#print axioms LatinonEntropy.correction_lemma
