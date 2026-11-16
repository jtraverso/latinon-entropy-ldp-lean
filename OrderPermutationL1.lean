module

public import OrderTransportIntegrals
public import GridPermutationPreserves

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem integrable_unit_coordinate (f : I → I) (hf : Measurable f) :
    Integrable (fun u => (f u : ℝ)) volume := by
  apply Integrable.of_bound (measurable_subtype_coe.comp hf).aestronglyMeasurable 1
  apply ae_of_all
  intro u
  change ‖(f u : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (f u).property.1]
  exact (f u).property.2

theorem order_fractional_cost_L1_bound {n : ℕ} (hn : 0 < n) (f : I → I)
    (hf : MeasurePreserving f volume volume) (a : Fin n → ℝ) :
    (∑ i, ∑ j, orderGridTransport f n i j*|a i-symbolGridLower j|) ≤
      (n : ℝ)*((∫ u : I, |(f u : ℝ)-a (unitGridIndex n hn u)|)+1/(n : ℝ)) := by
  have hF := integrable_unit_coordinate f hf.measurable
  have hA := finite_observation_integrable (volume : Measure I) _ (unitGridIndex_measurable n hn) a
  have hE : Integrable (fun u => |(f u : ℝ)-a (unitGridIndex n hn u)|) volume := (hF.sub hA).abs
  have hC : Integrable (fun u : I => |a (unitGridIndex n hn u)-symbolGridLower (unitGridIndex n hn (f u))|) volume :=
    finite_observation_integrable (volume : Measure I) _ (orderGridPairIndex_measurable hn f hf.measurable)
      (fun b : Fin n × Fin n => |a b.1-symbolGridLower b.2|)
  rw [order_grid_transport_pairing_integral hn f hf (fun i j => |a i-symbolGridLower j|)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  calc
    (∫ u : I, |a (unitGridIndex n hn u)-symbolGridLower (unitGridIndex n hn (f u))|)
        ≤ ∫ u : I, |(f u : ℝ)-a (unitGridIndex n hn u)|+1/(n : ℝ) := by
          apply integral_mono hC (hE.add (integrable_const _))
          intro u
          dsimp only [Pi.add_apply]
          have ht := abs_sub_le (a (unitGridIndex n hn u)) (f u : ℝ)
            (symbolGridLower (unitGridIndex n hn (f u)))
          rw [abs_sub_comm (a (unitGridIndex n hn u)) (f u : ℝ)] at ht
          exact ht.trans (add_le_add le_rfl (unitGridIndex_error n hn (f u)))
    _ = _ := by
      rw [integral_add hE (integrable_const _),integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]

theorem grid_permutation_L1_step_bound {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    (f : I → I) (hf : Measurable f) (a : Fin n → ℝ) :
    (∫ u : I, |(f u : ℝ)-(gridIntervalPermutation hn sigma u : ℝ)|) ≤
      (∫ u : I, |(f u : ℝ)-a (unitGridIndex n hn u)|)+
        (1/(n : ℝ))*(∑ i, |a i-symbolGridLower (sigma i)|)+1/(n : ℝ) := by
  have hF := integrable_unit_coordinate f hf
  have hH := integrable_unit_coordinate _ (gridIntervalPermutation_measurable hn sigma)
  have hA := finite_observation_integrable (volume : Measure I) _ (unitGridIndex_measurable n hn) a
  have hE : Integrable (fun u => |(f u : ℝ)-a (unitGridIndex n hn u)|) volume := (hF.sub hA).abs
  let c : Fin n → ℝ := fun i => |a i-symbolGridLower (sigma i)|
  have hC : Integrable (fun u => c (unitGridIndex n hn u)) volume :=
    finite_observation_integrable (volume : Measure I) _ (unitGridIndex_measurable n hn) c
  have hEC : Integrable (fun u => |(f u : ℝ)-a (unitGridIndex n hn u)|+c (unitGridIndex n hn u)) volume :=
    hE.add hC
  have hdiff : Integrable (fun u => |(f u : ℝ)-(gridIntervalPermutation hn sigma u : ℝ)|) volume := (hF.sub hH).abs
  calc
    (∫ u : I, |(f u : ℝ)-(gridIntervalPermutation hn sigma u : ℝ)|)
        ≤ ∫ u : I, (|(f u : ℝ)-a (unitGridIndex n hn u)|+c (unitGridIndex n hn u))+1/(n : ℝ) := by
          apply integral_mono_ae hdiff (hEC.add (integrable_const _))
          filter_upwards [lebesgueGridCell_cover_ae hn] with u hu
          obtain ⟨i,hi⟩ := hu
          dsimp only [Pi.add_apply]
          rw [unitGridIndex_of_mem hn hi]
          have hm := gridIntervalPermutation_cell hn sigma hi
          have herr : |(gridIntervalPermutation hn sigma u : ℝ)-symbolGridLower (sigma i)| ≤ 1/(n : ℝ) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hm.1.le)]
            linarith only [hm.2,symbolGrid_width (sigma i)]
          have h1 := abs_sub_le (f u : ℝ) (a i) (symbolGridLower (sigma i))
          have h2 := abs_sub_le (f u : ℝ) (symbolGridLower (sigma i)) (gridIntervalPermutation hn sigma u : ℝ)
          rw [abs_sub_comm (symbolGridLower (sigma i))] at h2
          dsimp only [c]
          linarith only [h1,h2,herr]
    _ = _ := by
      rw [integral_add hEC (integrable_const _),integral_add hE hC,integral_const,
        integral_unitGridIndex hn c]
      simp only [probReal_univ,smul_eq_mul,one_mul]
      rfl

/-- Birkhoff rounding gives an actual interval-permutation bijection,
whose L1 error is controlled by an arbitrary grid-step approximation. -/
theorem exists_grid_permutation_L1_bound {n : ℕ} (hn : 0 < n) (f : I → I)
    (hf : MeasurePreserving f volume volume) (a : Fin n → ℝ) :
    ∃ sigma : Equiv.Perm (Fin n),
      (∫ u : I, |(f u : ℝ)-(gridIntervalPermutation hn sigma u : ℝ)|) ≤
        2*(∫ u : I, |(f u : ℝ)-a (unitGridIndex n hn u)|)+2/(n : ℝ) := by
  let E := ∫ u : I, |(f u : ℝ)-a (unitGridIndex n hn u)|
  let c : Matrix (Fin n) (Fin n) ℝ := fun i j => |a i-symbolGridLower j|
  obtain ⟨sigma,hs⟩ := exists_order_grid_permutation_cost_le hn f hf c
  have hc := hs.trans (order_fractional_cost_L1_bound hn f hf a)
  have hscale := mul_le_mul_of_nonneg_left hc (div_nonneg zero_le_one (Nat.cast_nonneg n))
  have hR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne'
  have he : (1/(n : ℝ))*((n : ℝ)*(E+1/(n : ℝ))) = E+1/(n : ℝ) := by
    rw [← mul_assoc,one_div,inv_mul_cancel₀ hR,one_mul]
  change (1/(n : ℝ))*(∑ i, c i (sigma i)) ≤ (1/(n : ℝ))*((n : ℝ)*(E+1/(n : ℝ))) at hscale
  rw [he] at hscale
  refine ⟨sigma,?_⟩
  have hh := grid_permutation_L1_step_bound hn sigma f hf.measurable a
  change (∫ u : I, |(f u : ℝ)-(gridIntervalPermutation hn sigma u : ℝ)|) ≤
    E+(1/(n : ℝ))*(∑ i, c i (sigma i))+1/(n : ℝ) at hh
  dsimp only [E] at hh hscale
  simp only [div_eq_mul_inv,one_mul] at hh hscale ⊢
  linarith only [hh,hscale]

end LatinonEntropy

#print axioms LatinonEntropy.integrable_unit_coordinate
#print axioms LatinonEntropy.order_fractional_cost_L1_bound
#print axioms LatinonEntropy.grid_permutation_L1_step_bound
#print axioms LatinonEntropy.exists_grid_permutation_L1_bound
