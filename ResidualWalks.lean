module

public import SmallResidualStep

@[expose] public section

/-! Traversal multiplicities and conservation for the actual box residual
graph. A closed walk yields a circulation, including repeated coordinates. -/

noncomputable section

namespace LatinonEntropy

variable {Y Z : Type*}

def boxResidual (lower upper Q : Y → Z → ℝ) : Y ⊕ Z → Y ⊕ Z → Prop
  | .inl y, .inr z => Q y z < upper y z
  | .inr z, .inl y => lower y z < Q y z
  | _, _ => False

def boxResidualCost (M Q : Y → Z → ℝ) : Y ⊕ Z → Y ⊕ Z → ℝ
  | .inl y, .inr z => forwardCost (Q y z) (M y z)
  | .inr z, .inl y => backwardCost (Q y z) (M y z)
  | _, _ => 0

def pointMatrix (y : Y) (z : Z) : Y → Z → ℝ := by
  classical
  exact fun i j => if i = y then if j = z then 1 else 0 else 0

def rowMark (v : Y ⊕ Z) (y : Y) : ℝ := by
  classical
  exact match v with
    | .inl i => if y = i then 1 else 0
    | .inr _ => 0

def colMark (v : Y ⊕ Z) (z : Z) : ℝ := by
  classical
  exact match v with
    | .inl _ => 0
    | .inr j => if z = j then 1 else 0

theorem pointMatrix_nonneg (y : Y) (z : Z) (i : Y) (j : Z) :
    0 ≤ pointMatrix y z i j := by
  classical
  simp only [pointMatrix]
  split_ifs <;> norm_num

theorem pointMatrix_row [Fintype Z] (y : Y) (z : Z) (i : Y) :
    (∑ j, pointMatrix y z i j) = rowMark (Z := Z) (.inl y) i := by
  classical
  by_cases h : i = y <;> simp [pointMatrix, rowMark, h]

theorem pointMatrix_col [Fintype Y] (y : Y) (z : Z) (j : Z) :
    (∑ i, pointMatrix y z i j) = colMark (Y := Y) (.inr z) j := by
  classical
  by_cases h : j = z <;> simp [pointMatrix, colMark, h]

theorem pointMatrix_pairing [Fintype Y] [Fintype Z]
    (y : Y) (z : Z) (f : Y → Z → ℝ) :
    (∑ i, ∑ j, pointMatrix y z i j * f i j) = f y z := by
  classical
  simp [pointMatrix]

/-- Multiplicities of a residual walk, with exact endpoint divergence and
exact cost. Counts are nonnegative reals (in this construction integers). -/
theorem residual_walk_multiplicities
    [Fintype Y] [Fintype Z] (M lower upper Q : Y → Z → ℝ)
    {start finish : Y ⊕ Z} {t : ℝ} {n : ℕ}
    (walk : CostWalk (boxResidual lower upper Q) (boxResidualCost M Q) start finish t n) :
    ∃ a b : Y → Z → ℝ,
      (∀ y z, 0 ≤ a y z) ∧ (∀ y z, 0 ≤ b y z) ∧
      (∀ y z, 0 < a y z → Q y z < upper y z) ∧
      (∀ y z, 0 < b y z → lower y z < Q y z) ∧
      (∀ y, (∑ z, (a y z - b y z)) = rowMark start y - rowMark finish y) ∧
      (∀ z, (∑ y, (a y z - b y z)) = colMark finish z - colMark start z) ∧
      t = ∑ y, ∑ z, (a y z * forwardCost (Q y z) (M y z) +
        b y z * backwardCost (Q y z) (M y z)) := by
  classical
  induction walk with
  | nil =>
      refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp
  | @snoc vertex t n walk next edge ih =>
      obtain ⟨a, b, ha, hb, hf, hr, hrows, hcols, hcost⟩ := ih
      cases vertex with
      | inl y =>
          cases next with
          | inl i => exact False.elim edge
          | inr z =>
              let a' : Y → Z → ℝ := fun i j => a i j + pointMatrix y z i j
              refine ⟨a', b, ?_, hb, ?_, hr, ?_, ?_, ?_⟩
              · intro i j
                exact add_nonneg (ha i j) (pointMatrix_nonneg y z i j)
              · intro i j hp
                by_cases hi : i = y
                · subst i
                  by_cases hj : j = z
                  · subst j; exact edge
                  · exact hf y j (by simpa [a', pointMatrix, hj] using hp)
                · exact hf i j (by simpa [a', pointMatrix, hi] using hp)
              · intro i
                calc
                  (∑ j, (a' i j - b i j)) =
                      (∑ j, (a i j - b i j)) + ∑ j, pointMatrix y z i j := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro j _
                    dsimp [a']; ring
                  _ = rowMark start i - rowMark (.inr z) i := by
                    rw [hrows i, pointMatrix_row]
                    simp [rowMark]
              · intro j
                calc
                  (∑ i, (a' i j - b i j)) =
                      (∑ i, (a i j - b i j)) + ∑ i, pointMatrix y z i j := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro i _
                    dsimp [a']; ring
                  _ = colMark (.inr z) j - colMark start j := by
                    rw [hcols j, pointMatrix_col]
                    simp [colMark]
                    ring
              · change t + forwardCost (Q y z) (M y z) = _
                rw [hcost]
                dsimp [a']
                simp_rw [add_mul]
                simp only [Finset.sum_add_distrib]
                rw [pointMatrix_pairing]
                ring
      | inr z =>
          cases next with
          | inr j => exact False.elim edge
          | inl y =>
              let b' : Y → Z → ℝ := fun i j => b i j + pointMatrix y z i j
              refine ⟨a, b', ha, ?_, hf, ?_, ?_, ?_, ?_⟩
              · intro i j
                exact add_nonneg (hb i j) (pointMatrix_nonneg y z i j)
              · intro i j hp
                by_cases hi : i = y
                · subst i
                  by_cases hj : j = z
                  · subst j; exact edge
                  · exact hr y j (by simpa [b', pointMatrix, hj] using hp)
                · exact hr i j (by simpa [b', pointMatrix, hi] using hp)
              · intro i
                calc
                  (∑ j, (a i j - b' i j)) =
                      (∑ j, (a i j - b i j)) - ∑ j, pointMatrix y z i j := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro j _
                    dsimp [b']; ring
                  _ = rowMark start i - rowMark (.inl y) i := by
                    rw [hrows i, pointMatrix_row]
                    simp [rowMark]
              · intro j
                calc
                  (∑ i, (a i j - b' i j)) =
                      (∑ i, (a i j - b i j)) - ∑ i, pointMatrix y z i j := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro i _
                    dsimp [b']; ring
                  _ = colMark (.inl y) j - colMark start j := by
                    rw [hcols j, pointMatrix_col]
                    simp [colMark]
              · change t + backwardCost (Q y z) (M y z) = _
                rw [hcost]
                dsimp [b']
                simp_rw [add_mul]
                simp only [Finset.sum_add_distrib]
                rw [pointMatrix_pairing]
                ring

theorem boxResidualCost_le_one (M Q : Y → Z → ℝ) (u v : Y ⊕ Z) :
    boxResidualCost M Q u v ≤ 1 := by
  cases u <;> cases v <;> simp only [boxResidualCost, forwardCost, backwardCost]
  all_goals try split_ifs
  all_goals norm_num

/-- Optimality now implies absence of negative closed walks of the actual
residual graph. No circulation or positive-step hypothesis is assumed. -/
theorem residual_closed_walk_nonnegative
    [Fintype Y] [Fintype Z] [Nonempty Y] [Nonempty Z]
    (M lower upper Q : Y → Z → ℝ)
    (hbox : Q ∈ Set.Icc lower upper)
    (hrow : ∀ y, ∑ z, Q y z = 1) (hcol : ∀ z, ∑ y, Q y z = 1)
    (hmin : ∀ P : Y → Z → ℝ, P ∈ Set.Icc lower upper →
      (∀ y, ∑ z, P y z = 1) → (∀ z, ∑ y, P y z = 1) →
      (∑ y, ∑ z, |Q y z - M y z|) ≤ ∑ y, ∑ z, |P y z - M y z|)
    (v : Y ⊕ Z) (t : ℝ) (n : ℕ)
    (walk : CostWalk (boxResidual lower upper Q) (boxResidualCost M Q) v v t n) :
    0 ≤ t := by
  obtain ⟨a, b, ha, hb, hf, hr, hrows, hcols, hcost⟩ :=
    residual_walk_multiplicities M lower upper Q walk
  rw [hcost]
  apply residual_circulation_cost_nonnegative M lower upper Q a b hbox hrow hcol hmin
    ha hb hf hr
  · intro y
    simpa using hrows y
  · intro z
    simpa using hcols z

end LatinonEntropy

#print axioms LatinonEntropy.residual_walk_multiplicities
#print axioms LatinonEntropy.residual_closed_walk_nonnegative
