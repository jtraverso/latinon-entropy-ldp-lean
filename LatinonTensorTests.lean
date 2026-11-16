module

public import LatinonWeakMarginalCompactness

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem abs_mul_sub_mul_unit_le (a b c d : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    |a*b-c*d| = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |a-c| * |b|+|c| * |b-d| := by
      simpa only [abs_mul] using abs_add_le ((a-c)*b) (c*(b-d))
    _ ≤ |a-c|+|b-d| := by
      rw [abs_of_nonneg hb.1,abs_of_nonneg hc.1]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb.2)
        (mul_le_of_le_one_left (abs_nonneg _) hc.2)

theorem abs_triple_sub_triple_unit_le (a b c x y z : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |a*b*c-x*y*z| ≤ |a-x|+|b-y|+|c-z| := by
  have hxy : x*y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hx.1 hy.1,(mul_le_of_le_one_left hy.1 hx.2).trans hy.2⟩
  exact (abs_mul_sub_mul_unit_le (a*b) c (x*y) z hc hxy).trans
    (add_le_add (abs_mul_sub_mul_unit_le a b x y hb hx) le_rfl)

def latinonTensorTest (a b c : I → ℝ) (p : LatinonPoint) : ℝ :=
  a p.1.1*b p.1.2*c p.2

theorem latinonTensorTest_measurable (a b c : I → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (latinonTensorTest a b c) :=
  ((ha.comp (measurable_fst.comp measurable_fst)).mul
    (hb.comp (measurable_snd.comp measurable_fst))).mul (hc.comp measurable_snd)

theorem latinonTensorTest_bounds (a b c : I → ℝ)
    (ha : ∀ u, a u ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ u, b u ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ u, c u ∈ Set.Icc (0 : ℝ) 1) (p : LatinonPoint) :
    latinonTensorTest a b c p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg (mul_nonneg (ha _).1 (hb _).1) (hc _).1,
    (mul_le_of_le_one_left (hc _).1
      ((mul_le_of_le_one_left (hb _).1 (ha _).2).trans (hb _).2)).trans (hc _).2⟩

theorem latinon_integral_coordinate (W : LatinonMeasure) (coord : LatinonPoint → I)
    (hcoord : MeasurePreserving coord W.measure volume) (f : I → ℝ) (hf : Measurable f) :
    (∫ p, f (coord p) ∂W.measure) = ∫ u, f u := by
  rw [← integral_map hcoord.measurable.aemeasurable hf.aestronglyMeasurable,hcoord.map_eq]

/-- Rectangle indicators can be replaced by continuous coordinate tests with
an error controlled solely by the uniform one-coordinate margins. -/
theorem latinon_box_tensor_error (W : LatinonMeasure) (S T U : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (a b c : I → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (ha01 : ∀ u, a u ∈ Set.Icc (0 : ℝ) 1)
    (hb01 : ∀ u, b u ∈ Set.Icc (0 : ℝ) 1)
    (hc01 : ∀ u, c u ∈ Set.Icc (0 : ℝ) 1) :
    |W.measure.real ((S ×ˢ T) ×ˢ U)-(∫ p, latinonTensorTest a b c p ∂W.measure)| ≤
      (∫ u, |S.indicator (fun _ => (1 : ℝ)) u-a u|)+
      (∫ u, |T.indicator (fun _ => (1 : ℝ)) u-b u|)+
      (∫ u, |U.indicator (fun _ => (1 : ℝ)) u-c u|) := by
  have hrow : MeasurePreserving (fun p : LatinonPoint => p.1.1) W.measure volume :=
    measurePreserving_fst.comp (latinon_xy_preserving W)
  have hcol : MeasurePreserving (fun p : LatinonPoint => p.1.2) W.measure volume :=
    measurePreserving_snd.comp (latinon_xy_preserving W)
  have hsymbol : MeasurePreserving (fun p : LatinonPoint => p.2) W.measure volume :=
    (measurePreserving_snd (μ := (volume : Measure I)) (ν := volume)).comp (latinon_xz_preserving W)
  let s : I → ℝ := S.indicator (fun _ => (1 : ℝ))
  let t : I → ℝ := T.indicator (fun _ => (1 : ℝ))
  let v : I → ℝ := U.indicator (fun _ => (1 : ℝ))
  have hs : Measurable s := measurable_const.indicator hS
  have ht : Measurable t := measurable_const.indicator hT
  have hv : Measurable v := measurable_const.indicator hU
  have hs01 (u : I) : s u ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : u ∈ S <;> simp [s,h]
  have ht01 (u : I) : t u ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : u ∈ T <;> simp [t,h]
  have hv01 (u : I) : v u ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : u ∈ U <;> simp [v,h]
  have hunit (f : I → ℝ) (hm : Measurable f) (h01 : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) :
      Integrable f volume := Integrable.of_mem_Icc 0 1 hm.aemeasurable (ae_of_all volume h01)
  have hsi := (hunit s hs hs01).sub (hunit a ha ha01)
  have hti := (hunit t ht ht01).sub (hunit b hb hb01)
  have hvi := (hunit v hv hv01).sub (hunit c hc hc01)
  have hxi : Integrable (fun p : LatinonPoint => |s p.1.1-a p.1.1|) W.measure :=
    hrow.integrable_comp_of_integrable hsi.abs
  have hyi : Integrable (fun p : LatinonPoint => |t p.1.2-b p.1.2|) W.measure :=
    hcol.integrable_comp_of_integrable hti.abs
  have hzi : Integrable (fun p : LatinonPoint => |v p.2-c p.2|) W.measure :=
    hsymbol.integrable_comp_of_integrable hvi.abs
  have hten : Integrable (latinonTensorTest a b c) W.measure :=
    Integrable.of_mem_Icc 0 1 (latinonTensorTest_measurable a b c ha hb hc).aemeasurable
      (ae_of_all W.measure (latinonTensorTest_bounds a b c ha01 hb01 hc01))
  have hind : Integrable (((S ×ˢ T) ×ˢ U).indicator (fun _ => (1 : ℝ))) W.measure :=
    (integrable_const (1 : ℝ)).indicator ((hS.prod hT).prod hU)
  have hind_eq (p : LatinonPoint) :
      ((S ×ˢ T) ×ˢ U).indicator (fun _ => (1 : ℝ)) p=latinonTensorTest s t v p := by
    by_cases h1 : p.1.1 ∈ S <;> by_cases h2 : p.1.2 ∈ T <;> by_cases h3 : p.2 ∈ U <;>
      simp [latinonTensorTest,s,t,v,Set.mem_prod,h1,h2,h3]
  have he : W.measure.real ((S ×ˢ T) ×ˢ U)=
      ∫ p, ((S ×ˢ T) ×ˢ U).indicator (fun _ => (1 : ℝ)) p ∂W.measure :=
    (integral_indicator_one ((hS.prod hT).prod hU)).symm
  rw [he,← integral_sub hind hten]
  calc
    _ ≤ ∫ p, |((S ×ˢ T) ×ˢ U).indicator (fun _ => (1 : ℝ)) p-
        latinonTensorTest a b c p| ∂W.measure := abs_integral_le_integral_abs
    _ ≤ ∫ p, (|s p.1.1-a p.1.1|+|t p.1.2-b p.1.2|)+|v p.2-c p.2| ∂W.measure := by
      apply integral_mono (hind.sub hten).abs ((hxi.add hyi).add hzi)
      intro p
      change |((S ×ˢ T) ×ˢ U).indicator (fun _ => (1 : ℝ)) p-latinonTensorTest a b c p| ≤
        |s p.1.1-a p.1.1|+|t p.1.2-b p.1.2|+|v p.2-c p.2|
      rw [hind_eq]
      exact abs_triple_sub_triple_unit_le _ _ _ _ _ _ (ht01 _) (hv01 _) (ha01 _) (hb01 _)
    _ = _ := by
      rw [integral_add (f := fun p : LatinonPoint => |s p.1.1-a p.1.1|+|t p.1.2-b p.1.2|)
          (hxi.add hyi) hzi,integral_add hxi hyi,
        latinon_integral_coordinate W _ hrow (fun u => |s u-a u|)
          (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hs.sub ha).norm),
        latinon_integral_coordinate W _ hcol (fun u => |t u-b u|)
          (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using (ht.sub hb).norm),
        latinon_integral_coordinate W _ hsymbol (fun u => |v u-c u|)
          (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hv.sub hc).norm)]

end LatinonEntropy

#print axioms LatinonEntropy.abs_mul_sub_mul_unit_le
#print axioms LatinonEntropy.abs_triple_sub_triple_unit_le
#print axioms LatinonEntropy.latinonTensorTest_measurable
#print axioms LatinonEntropy.latinonTensorTest_bounds
#print axioms LatinonEntropy.latinon_integral_coordinate
#print axioms LatinonEntropy.latinon_box_tensor_error
