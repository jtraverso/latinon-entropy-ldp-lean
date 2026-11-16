module

public import ResidualOptimality

@[expose] public section

/-! A common positive step for finitely many residual coordinates, and the
nonnegative cost of every feasible residual circulation at an L1 optimizer.
Repeated forward/backward use of a coordinate is allowed. -/

noncomputable section

namespace LatinonEntropy

def SafeResidualStep (q m lower upper a b delta : ℝ) : Prop :=
  (lower ≤ q + delta * (a - b) ∧ q + delta * (a - b) ≤ upper) ∧
  (q < m → q + delta * (a - b) ≤ m) ∧
  (m < q → m ≤ q + delta * (a - b))

theorem exists_coordinate_residual_step
    (q m lower upper a b : ℝ)
    (hlo : lower ≤ q) (hhi : q ≤ upper) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hforward : 0 < a → q < upper) (hbackward : 0 < b → lower < q) :
    ∃ eta > 0, ∀ delta, 0 ≤ delta → delta ≤ eta →
      SafeResidualStep q m lower upper a b delta := by
  classical
  let B := a + b + 1
  let u := if 0 < a then upper - q else 1
  let l := if 0 < b then q - lower else 1
  let s := if q = m then 1 else |q - m|
  have hB : 0 < B := by dsimp [B]; linarith
  have hu : 0 < u := by
    dsimp [u]
    split_ifs with h
    · exact sub_pos.mpr (hforward h)
    · exact zero_lt_one
  have hl : 0 < l := by
    dsimp [l]
    split_ifs with h
    · exact sub_pos.mpr (hbackward h)
    · exact zero_lt_one
  have hs : 0 < s := by
    dsimp [s]
    split_ifs with h
    · exact zero_lt_one
    · exact abs_pos.mpr (sub_ne_zero.mpr h)
  refine ⟨min u (min l s) / B, div_pos (lt_min hu (lt_min hl hs)) hB, ?_⟩
  intro delta hd hdelta
  have hbound : delta * B ≤ min u (min l s) := (le_div_iff₀ hB).mp hdelta
  have hdu : delta * B ≤ u := hbound.trans (min_le_left _ _)
  have hdl : delta * B ≤ l := hbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hds : delta * B ≤ s := hbound.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp : delta * (a - b) ≤ delta * B :=
    mul_le_mul_of_nonneg_left (by dsimp [B]; linarith) hd
  have hn : delta * (b - a) ≤ delta * B :=
    mul_le_mul_of_nonneg_left (by dsimp [B]; linarith) hd
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · by_cases hbpos : 0 < b
    · have hh : delta * B ≤ q - lower := by simpa [l, hbpos] using hdl
      nlinarith
    · have hbzero : b = 0 := le_antisymm (le_of_not_gt hbpos) hb
      have hh : 0 ≤ delta * a := mul_nonneg hd ha
      simp only [hbzero, sub_zero]
      linarith
  · by_cases hapos : 0 < a
    · have hh : delta * B ≤ upper - q := by simpa [u, hapos] using hdu
      linarith
    · have hazero : a = 0 := le_antisymm (le_of_not_gt hapos) ha
      have hh : 0 ≤ delta * b := mul_nonneg hd hb
      simp only [hazero, zero_sub, mul_neg]
      linarith
  · intro hqm
    have hne : q ≠ m := ne_of_lt hqm
    have hh : delta * B ≤ m - q := by
      simpa [s, hne, abs_of_neg (sub_neg.mpr hqm)] using hds
    linarith
  · intro hmq
    have hne : q ≠ m := ne_of_gt hmq
    have hh : delta * B ≤ q - m := by
      simpa [s, hne, abs_of_pos (sub_pos.mpr hmq)] using hds
    nlinarith

/-- Finiteness yields one positive step for all coordinates simultaneously. -/
theorem exists_common_residual_step
    {I : Type*} [Finite I] [Nonempty I]
    (q m lower upper a b : I → ℝ)
    (hlo : ∀ i, lower i ≤ q i) (hhi : ∀ i, q i ≤ upper i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hforward : ∀ i, 0 < a i → q i < upper i)
    (hbackward : ∀ i, 0 < b i → lower i < q i) :
    ∃ delta > 0, ∀ i, SafeResidualStep (q i) (m i) (lower i) (upper i) (a i) (b i) delta := by
  classical
  have hlocal := fun i => exists_coordinate_residual_step
    (q i) (m i) (lower i) (upper i) (a i) (b i)
    (hlo i) (hhi i) (ha i) (hb i) (hforward i) (hbackward i)
  choose eta hpos hsafe using hlocal
  obtain ⟨i0, hmin⟩ := Finite.exists_min eta
  exact ⟨eta i0, hpos i0, fun i => hsafe i (eta i0) (hpos i0).le (hmin i)⟩

/-- At a box-constrained L1 minimizer every residual circulation has
nonnegative cost. Positivity of a common feasible step is proved above,
rather than assumed. Zero row/column divergence is explicit here. -/
theorem residual_circulation_cost_nonnegative
    {Y Z : Type*} [Fintype Y] [Fintype Z] [Nonempty Y] [Nonempty Z]
    (M lower upper Q a b : Y → Z → ℝ)
    (hbox : Q ∈ Set.Icc lower upper)
    (hrow : ∀ y, ∑ z, Q y z = 1) (hcol : ∀ z, ∑ y, Q y z = 1)
    (hmin : ∀ P : Y → Z → ℝ, P ∈ Set.Icc lower upper →
      (∀ y, ∑ z, P y z = 1) → (∀ z, ∑ y, P y z = 1) →
      (∑ y, ∑ z, |Q y z - M y z|) ≤ ∑ y, ∑ z, |P y z - M y z|)
    (ha : ∀ y z, 0 ≤ a y z) (hb : ∀ y z, 0 ≤ b y z)
    (hforward : ∀ y z, 0 < a y z → Q y z < upper y z)
    (hbackward : ∀ y z, 0 < b y z → lower y z < Q y z)
    (hrows : ∀ y, ∑ z, (a y z - b y z) = 0)
    (hcols : ∀ z, ∑ y, (a y z - b y z) = 0) :
    0 ≤ ∑ y, ∑ z, (a y z * forwardCost (Q y z) (M y z) +
      b y z * backwardCost (Q y z) (M y z)) := by
  obtain ⟨delta, hd, hstep⟩ := exists_common_residual_step
    (fun i : Y × Z => Q i.1 i.2) (fun i => M i.1 i.2)
    (fun i => lower i.1 i.2) (fun i => upper i.1 i.2)
    (fun i => a i.1 i.2) (fun i => b i.1 i.2)
    (fun i => hbox.1 i.1 i.2) (fun i => hbox.2 i.1 i.2)
    (fun i => ha i.1 i.2) (fun i => hb i.1 i.2)
    (fun i => hforward i.1 i.2) (fun i => hbackward i.1 i.2)
  let P : Y → Z → ℝ := fun y z => Q y z + delta * (a y z - b y z)
  have hPbox : P ∈ Set.Icc lower upper :=
    ⟨fun y z => (hstep (y,z)).1.1, fun y z => (hstep (y,z)).1.2⟩
  have hProw : ∀ y, ∑ z, P y z = 1 := by
    intro y
    simp only [P, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hrows, mul_zero, add_zero]
  have hPcol : ∀ z, ∑ y, P y z = 1 := by
    intro z
    simp only [P, Finset.sum_add_distrib, ← Finset.mul_sum, hcol, hcols, mul_zero, add_zero]
  have hcost := hmin P hPbox hProw hPcol
  have hh := nonnegative_residual_cost_of_step
    (fun i : Y × Z => Q i.1 i.2) (fun i => M i.1 i.2)
    (fun i => a i.1 i.2) (fun i => b i.1 i.2) delta
    (fun i => ha i.1 i.2) (fun i => hb i.1 i.2) hd
    (fun i => (hstep i).2.1) (fun i => (hstep i).2.2)
    (by simpa only [Fintype.sum_prod_type, P] using hcost)
  simpa only [Fintype.sum_prod_type] using hh

end LatinonEntropy

#print axioms LatinonEntropy.exists_common_residual_step
#print axioms LatinonEntropy.residual_circulation_cost_nonnegative
