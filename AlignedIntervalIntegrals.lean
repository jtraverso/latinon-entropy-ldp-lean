module

public import MeasurableIntervalRounding
public import FiniteRectangleIntegrals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

/-- The interval evaluation of the finite Latin step function. It is zero
on the null row/column grid boundary at0; a probability-kernel representative
will be identified almost everywhere when constructing the Latinon object. -/
def finiteLatinIntervalStep {n : ℕ} (L : LatinArray n) (a b : ℝ) (u v : I) : ℝ :=
  finiteRectangleStep lebesgueGridCell lebesgueGridCell
    (fun i j => symbolIntervalWeight (L.val i j) a b) u v

theorem finiteLatinIntervalStep_aligned_eq {n : ℕ} (L : LatinArray n) (a b : ℝ)
    (phi psi : I → I) (u v : I) :
    finiteLatinIntervalStep L a b (phi u) (psi v) =
      finiteRectangleStep (fun i => phi ⁻¹' lebesgueGridCell i)
        (fun j => psi ⁻¹' lebesgueGridCell j)
        (fun i j => symbolIntervalWeight (L.val i j) a b) u v := by
  rfl

/-- Exact cut integral of the aligned finite step, with the actual
intersection weights. The normalization n^-2 cancels the two factors n. -/
theorem aligned_finite_interval_integral_eq_table {n r s t : ℕ} (hn : 0 < n)
    (P : SymbolIntervalPartition t)
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (phi psi : I → I) (hphi : MeasurePreserving phi volume volume)
    (hpsi : MeasurePreserving psi volume volume) (L : LatinArray n) (z : LatinBlock r s t) :
    (∫ u in A.cell z.1.1, ∫ v in B.cell z.1.2,
      finiteLatinIntervalStep L (P.left z.2) (P.right z.2) (phi u) (psi v)) =
      alignedLatinIntervalTable P A B phi psi L z := by
  simp_rw [finiteLatinIntervalStep_aligned_eq]
  rw [finiteRectangleStep_rectangle_integral volume (A.cell z.1.1) (B.cell z.1.2)
    (fun i => phi ⁻¹' lebesgueGridCell i) (fun j => psi ⁻¹' lebesgueGridCell j)
    (fun i => (lebesgueGridCell_measurable i).preimage hphi.measurable)
    (fun j => (lebesgueGridCell_measurable j).preimage hpsi.measurable)]
  unfold alignedLatinIntervalTable latinIntervalFractionalTable latinIntervalWeightedCount lebesgueAlignmentWeight
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro j _
  apply (eq_div_iff (pow_ne_zero 2 (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne')).mpr
  ring

theorem exists_uniform_aligned_integral_rounding {t : ℕ} (P : SymbolIntervalPartition t)
    (r s : ℕ) (tau : ℝ) (htau : 0 < tau) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (A : MeasurableFinitePartition (volume : Measure I) r)
        (B : MeasurableFinitePartition (volume : Measure I) s) (phi psi : I → I),
      MeasurePreserving phi volume volume → MeasurePreserving psi volume volume →
      ∀ L : LatinArray n, ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
            (∫ u in A.cell z.1.1, ∫ v in B.cell z.1.2,
              finiteLatinIntervalStep L (P.left z.2) (P.right z.2) (phi u) (psi v))| < tau) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-volume.real (A.cell a)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-volume.real (B.cell b)| < tau) ∧
        (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ)) := by
  obtain ⟨N,hN,hround⟩ := exists_uniform_measurable_interval_rounding P r s tau htau M
  refine ⟨N,hN,?_⟩
  intro n hn A B phi psi hphi hpsi L
  obtain ⟨row,col,hb,hr,hc,hsize⟩ := hround n hn A B phi psi hphi hpsi L
  refine ⟨row,col,?_,hr,hc,hsize⟩
  intro z
  rw [aligned_finite_interval_integral_eq_table (hN.trans_le hn) P A B phi psi hphi hpsi L z]
  exact hb z

end LatinonEntropy

#print axioms LatinonEntropy.finite_indicator_setIntegral
#print axioms LatinonEntropy.finiteRectangleStep_inner_integral
#print axioms LatinonEntropy.finiteRectangleStep_rectangle_integral
#print axioms LatinonEntropy.finiteLatinIntervalStep_aligned_eq
#print axioms LatinonEntropy.aligned_finite_interval_integral_eq_table
#print axioms LatinonEntropy.exists_uniform_aligned_integral_rounding
