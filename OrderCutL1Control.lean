module

public import LatinonCutNorms
public import OrderPermutationL1

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem mp_order_tail_integral (f : I → I) (hf : MeasurePreserving f volume volume) (a : I) :
    (∫ v : I, if a < f v then (1 : ℝ) else 0) = 1-(a : ℝ) := by
  have hm : MeasurableSet (f ⁻¹' Set.Ioi a) := hf.measurable (measurableSet_Ioi)
  change (∫ v : I, (f ⁻¹' Set.Ioi a).indicator (fun _ => (1 : ℝ)) v) = _
  rw [integral_indicator hm,setIntegral_const,smul_eq_mul,mul_one,
    hf.measureReal_preimage measurableSet_Ioi.nullMeasurableSet,
    measureReal_def,unitInterval.volume_Ioi,
    ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]

theorem orderBox_full_cols (f : I → I) (hf : MeasurePreserving f volume volume)
    (S : Set I) (hS : MeasurableSet S) :
    orderBox f ⟨S,Set.univ,hS,MeasurableSet.univ⟩ = ∫ u in S, 1-(f u : ℝ) := by
  rw [orderBox_eq_integral f hf.measurable]
  simp only [Measure.restrict_univ]
  simp_rw [mp_order_tail_integral f hf]

theorem abs_setIntegral_order_difference_le (f g : I → I)
    (hf : MeasurePreserving f volume volume) (hg : MeasurePreserving g volume volume)
    (S : Set I) (hS : MeasurableSet S) :
    |∫ u in S, (f u : ℝ)-(g u : ℝ)| ≤ orderCut f g := by
  let R : LatinonRectangle := ⟨S,Set.univ,hS,MeasurableSet.univ⟩
  have hF : Integrable (fun u : I => 1-(f u : ℝ)) volume :=
    (integrable_const 1).sub (integrable_unit_coordinate f hf.measurable)
  have hG : Integrable (fun u : I => 1-(g u : ℝ)) volume :=
    (integrable_const 1).sub (integrable_unit_coordinate g hg.measurable)
  have he : orderBox f R-orderBox g R = -(∫ u in S, (f u : ℝ)-(g u : ℝ)) := by
    rw [orderBox_full_cols f hf S hS,orderBox_full_cols g hg S hS,
      ← integral_sub hF.integrableOn hG.integrableOn,← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  have hb := orderCut_test_le f g R
  simpa only [he,abs_neg] using hb

theorem integral_abs_le_twice_setIntegral_bound {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (h : α → ℝ) (hm : Measurable h) (hi : Integrable h mu) (C : ℝ)
    (hC : ∀ S, MeasurableSet S → |∫ x in S, h x ∂mu| ≤ C) :
    (∫ x, |h x| ∂mu) ≤ 2*C := by
  have hp := (abs_le.mp (hC {x | 0 ≤ h x} (measurableSet_le measurable_const hm))).2
  have hn := (abs_le.mp (hC {x | h x ≤ 0} (measurableSet_le hm measurable_const))).1
  have he := integral_norm_eq_pos_sub_neg hi
  simp only [Real.norm_eq_abs] at he
  linarith only [hp,hn,he]

/-- The order cut metric controls the actual L1 distance of MP order maps.
This prevents loss of the order map when taking aligned Cauchy limits. -/
theorem orderCut_controls_L1 (f g : I → I)
    (hf : MeasurePreserving f volume volume) (hg : MeasurePreserving g volume volume) :
    (∫ u : I, |(f u : ℝ)-(g u : ℝ)|) ≤ 2*orderCut f g := by
  apply integral_abs_le_twice_setIntegral_bound volume (fun u : I => (f u : ℝ)-(g u : ℝ))
    ((measurable_subtype_coe.comp hf.measurable).sub (measurable_subtype_coe.comp hg.measurable))
    ((integrable_unit_coordinate f hf.measurable).sub (integrable_unit_coordinate g hg.measurable))
  exact abs_setIntegral_order_difference_le f g hf hg

end LatinonEntropy

#print axioms LatinonEntropy.mp_order_tail_integral
#print axioms LatinonEntropy.orderBox_full_cols
#print axioms LatinonEntropy.abs_setIntegral_order_difference_le
#print axioms LatinonEntropy.integral_abs_le_twice_setIntegral_bound
#print axioms LatinonEntropy.orderCut_controls_L1
