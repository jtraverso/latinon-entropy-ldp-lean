module

public import AllSizesOrderPermutation
public import UnitOrderDisagreement
public import LatinonRelabel
public import LatinonCutNorms

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem orderCut_le_disagreement (f g : I → I) :
    orderCut f g ≤ ((volume : Measure I).prod volume).real (unitOrderDisagreement f g) := by
  let mu : Measure (I × I) := (volume : Measure I).prod volume
  apply cutValueSup_le
  intro R
  let A := (R.rows ×ˢ R.cols) ∩ orderRelation f
  let B := (R.rows ×ˢ R.cols) ∩ orderRelation g
  have hab : A \ B ⊆ unitOrderDisagreement f g := by
    intro p hp
    exact Or.inl ⟨hp.1.2,fun h => hp.2 ⟨hp.1.1,h⟩⟩
  have hba : B \ A ⊆ unitOrderDisagreement f g := by
    intro p hp
    exact Or.inr ⟨hp.1.2,fun h => hp.2 ⟨hp.1.1,h⟩⟩
  have h1 : mu.real A-mu.real B ≤ mu.real (unitOrderDisagreement f g) :=
    (le_measureReal_sdiff (μ := mu) (s₁ := A) (s₂ := B)).trans (measureReal_mono hab)
  have h2 : mu.real B-mu.real A ≤ mu.real (unitOrderDisagreement f g) :=
    (le_measureReal_sdiff (μ := mu) (s₁ := B) (s₂ := A)).trans (measureReal_mono hba)
  change |mu.real A-mu.real B| ≤ _
  exact abs_le.mpr ⟨by linarith only [h2],h1⟩

theorem orderCut_L1_bound (f g : I → I) (hf : MeasurePreserving f volume volume)
    (hg : Measurable g) (t : ℝ) (ht : 0 < t) :
    t*orderCut f g ≤ 4*t^2+2*(∫ u : I, |(f u : ℝ)-(g u : ℝ)|) :=
  (mul_le_mul_of_nonneg_left (orderCut_le_disagreement f g) ht.le).trans
    (unitOrderDisagreement_L1_bound f g hf hg t ht)

def gridIntervalRelabel {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) : LatinonRelabel :=
  ⟨gridIntervalMeasurableEquiv hn sigma,gridIntervalPermutation_preserves hn sigma⟩

/-- All sufficiently large sizes admit actual admissible relabelings
that approximate the order term used in the full Latinon distance. -/
theorem exists_all_sizes_orderCut_permutation (f : I → I)
    (hf : MeasurePreserving f volume volume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∃ sigma : Equiv.Perm (Fin n), orderCut f (gridIntervalRelabel (hN.trans_le hn) sigma) < eps := by
  obtain ⟨N,hN,happrox⟩ := exists_all_sizes_order_permutation_L1 f hf (eps^2/256) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn
  obtain ⟨sigma,_,hL1⟩ := happrox n hn
  refine ⟨sigma,?_⟩
  have hb := orderCut_L1_bound f (gridIntervalPermutation (hN.trans_le hn) sigma) hf
    (gridIntervalPermutation_measurable (hN.trans_le hn) sigma) (eps/16) (by positivity)
  change (eps/16)*orderCut f (gridIntervalRelabel (hN.trans_le hn) sigma) ≤ _ at hb
  by_contra hnot
  have hge := le_of_not_gt hnot
  have hscaled := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ eps/16)
  nlinarith only [hb,hL1,hscaled,sq_pos_of_pos heps]

end LatinonEntropy

#print axioms LatinonEntropy.orderCut_le_disagreement
#print axioms LatinonEntropy.orderCut_L1_bound
#print axioms LatinonEntropy.gridIntervalRelabel
#print axioms LatinonEntropy.exists_all_sizes_orderCut_permutation
