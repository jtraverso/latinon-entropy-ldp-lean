module

public import OrderGridTransport
public import GridCoordinateIndex
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem unitGridIndex_membership_ae {n : ℕ} (hn : 0 < n) :
    ∀ᵐ u : I ∂volume, ∀ i : Fin n, unitGridIndex n hn u = i ↔ u ∈ lebesgueGridCell i := by
  filter_upwards [lebesgueGridCell_cover_ae hn] with u hu
  intro i
  exact finiteCellIndex_eq_iff_of_covered lebesgueGridCell ⟨0,hn⟩ (lebesgueGridCell_disjoint hn) hu i

theorem unitGridIndex_map_atom {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ((volume : Measure I).map (unitGridIndex n hn)) {i} = volume (lebesgueGridCell i) := by
  rw [Measure.map_apply (unitGridIndex_measurable n hn) (measurableSet_singleton i)]
  apply measure_congr
  filter_upwards [unitGridIndex_membership_ae hn] with u hu
  exact propext (hu i)

theorem finite_observation_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [MeasurableSingletonClass β] (mu : Measure α) [IsFiniteMeasure mu]
    (g : α → β) (hg : Measurable g) (a : β → ℝ) :
    Integrable (fun x => a (g x)) mu :=
  (Integrable.of_finite (μ := mu.map g) (f := a)).comp_measurable hg

theorem integral_unitGridIndex {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∫ u : I, a (unitGridIndex n hn u)) = (1/(n : ℝ))*(∑ i, a i) := by
  rw [← integral_map_of_stronglyMeasurable (unitGridIndex_measurable n hn)
    (measurable_of_countable a).stronglyMeasurable,integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul,measureReal_def,unitGridIndex_map_atom hn]
  change (∑ i, (volume : Measure I).real (lebesgueGridCell i)*a i) = _
  simp_rw [lebesgueGridCell_mass hn]
  exact (mul_sum _ _ _).symm

def orderGridPairIndex {n : ℕ} (hn : 0 < n) (f : I → I) (u : I) : Fin n × Fin n :=
  (unitGridIndex n hn u,unitGridIndex n hn (f u))

theorem orderGridPairIndex_measurable {n : ℕ} (hn : 0 < n) (f : I → I) (hf : Measurable f) :
    Measurable (orderGridPairIndex hn f) :=
  (unitGridIndex_measurable n hn).prodMk ((unitGridIndex_measurable n hn).comp hf)

theorem orderGridPairIndex_map_atom {n : ℕ} (hn : 0 < n) (f : I → I)
    (hf : MeasurePreserving f volume volume) (i j : Fin n) :
    ((volume : Measure I).map (orderGridPairIndex hn f)) {(i,j)} =
      volume (lebesgueGridCell i ∩ f ⁻¹' lebesgueGridCell j) := by
  rw [Measure.map_apply (orderGridPairIndex_measurable hn f hf.measurable) (measurableSet_singleton _)]
  apply measure_congr
  filter_upwards [unitGridIndex_membership_ae hn,hf.quasiMeasurePreserving.ae
    (unitGridIndex_membership_ae hn)] with u hu hv
  apply propext
  simp only [Set.mem_preimage,Set.mem_singleton_iff,orderGridPairIndex,Prod.mk.injEq,Set.mem_inter_iff]
  exact and_congr (hu i) (hv j)

theorem order_grid_transport_pairing_integral {n : ℕ} (hn : 0 < n) (f : I → I)
    (hf : MeasurePreserving f volume volume) (c : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, orderGridTransport f n i j*c i j) =
      (n : ℝ)*(∫ u : I, c (unitGridIndex n hn u) (unitGridIndex n hn (f u))) := by
  have hi := integral_map_of_stronglyMeasurable
    (μ := (volume : Measure I)) (orderGridPairIndex_measurable hn f hf.measurable)
    (measurable_of_countable (fun b : Fin n × Fin n => c b.1 b.2)).stronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at hi
  simp only [smul_eq_mul,measureReal_def] at hi
  simp_rw [orderGridPairIndex_map_atom hn f hf] at hi
  rw [Fintype.sum_prod_type] at hi
  change (∑ i, ∑ j, (volume : Measure I).real (lebesgueGridCell i ∩ f ⁻¹' lebesgueGridCell j)*c i j) =
    (∫ u : I, c (unitGridIndex n hn u) (unitGridIndex n hn (f u))) at hi
  rw [← hi]
  simp only [orderGridTransport,mul_sum,mul_assoc]

end LatinonEntropy

#print axioms LatinonEntropy.unitGridIndex_membership_ae
#print axioms LatinonEntropy.unitGridIndex_map_atom
#print axioms LatinonEntropy.finite_observation_integrable
#print axioms LatinonEntropy.integral_unitGridIndex
#print axioms LatinonEntropy.orderGridPairIndex_measurable
#print axioms LatinonEntropy.orderGridPairIndex_map_atom
#print axioms LatinonEntropy.order_grid_transport_pairing_integral
