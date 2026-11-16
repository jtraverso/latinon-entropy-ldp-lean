module

public import LatinonMeasureAlignment
public import FiniteLatinMeasureIntervals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

theorem relabelled_finite_interval_integral {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (e f : LatinonRelabel) (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) (a b : ℝ) :
    (relabelLatinonMeasure (latinArrayToLatinonMeasure hn L).measure e f).real
      ((S ×ˢ T) ×ˢ unitSymbolInterval a b) =
        ∫ u in S, ∫ v in T, finiteLatinIntervalStep L a b (e u) (f v) := by
  rw [relabelLatinonMeasure_real_box _ e f S T _ hS hT (unitSymbolInterval_measurable a b)]
  change (finiteLatinMeasure L).real (((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T)) ×ˢ unitSymbolInterval a b) = _
  rw [finiteLatinMeasure_real_box]
  simp_rw [finiteLatinIntervalStep_aligned_eq]
  rw [finiteRectangleStep_rectangle_integral volume S T
    (fun i => e ⁻¹' lebesgueGridCell i) (fun j => f ⁻¹' lebesgueGridCell j)
    (fun i => (lebesgueGridCell_measurable i).preimage e.measurable)
    (fun j => (lebesgueGridCell_measurable j).preimage f.measurable)]
  have he : ∀ x : Fin n, volume.real (e.symm ⁻¹' S ∩ lebesgueGridCell x) =
      volume.real (S ∩ e ⁻¹' lebesgueGridCell x) :=
    fun x => e.inverse_image_inter_mass S _ hS (lebesgueGridCell_measurable x)
  have hf : ∀ y : Fin n, volume.real (f.symm ⁻¹' T ∩ lebesgueGridCell y) =
      volume.real (T ∩ f ⁻¹' lebesgueGridCell y) :=
    fun y => f.inverse_image_inter_mass T _ hT (lebesgueGridCell_measurable y)
  simp_rw [he,hf,symbolIntervalWeight_eq_grid_interval_measure hn]
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  ring

theorem relabelled_finite_block_table {n r s t : ℕ} (hn : 0 < n)
    (P : SymbolIntervalPartition t)
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (e f : LatinonRelabel) (L : LatinArray n) (z : LatinBlock r s t) :
    (relabelLatinonMeasure (finiteLatinMeasure L) e f).real
      ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2)) =
      alignedLatinIntervalTable P A B e f L z :=
  (relabelled_finite_interval_integral hn L e f _ _ (A.measurable _) (B.measurable _) _ _).trans
    (aligned_finite_interval_integral_eq_table hn P A B e f e.preserves f.preserves L z)

/-- Actual transported measure masses, with one order threshold preceding
all target partitions, measurable bijections and Latin squares. -/
theorem exists_uniform_relabelled_measure_rounding {t : ℕ} (P : SymbolIntervalPartition t)
    (r s : ℕ) (tau : ℝ) (htau : 0 < tau) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (A : MeasurableFinitePartition (volume : Measure I) r)
        (B : MeasurableFinitePartition (volume : Measure I) s) (e f : LatinonRelabel),
      ∀ L : LatinArray n, ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
            (relabelLatinonMeasure (finiteLatinMeasure L) e f).real
              ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2))| < tau) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-volume.real (A.cell a)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-volume.real (B.cell b)| < tau) ∧
        (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ)) := by
  obtain ⟨N,hN,hround⟩ := exists_uniform_measurable_interval_rounding P r s tau htau M
  refine ⟨N,hN,?_⟩
  intro n hn A B e f L
  obtain ⟨row,col,hb,hr,hc,hsize⟩ := hround n hn A B e f e.preserves f.preserves L
  refine ⟨row,col,?_,hr,hc,hsize⟩
  intro z
  rw [relabelled_finite_block_table (hN.trans_le hn) P A B e f L z]
  exact hb z

end LatinonEntropy

#print axioms LatinonEntropy.relabelled_finite_interval_integral
#print axioms LatinonEntropy.relabelled_finite_block_table
#print axioms LatinonEntropy.exists_uniform_relabelled_measure_rounding
