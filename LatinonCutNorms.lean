module

public import FiniteLatinMeasureIntervals
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

structure LatinonRectangle where
  rows : Set I
  cols : Set I
  rows_measurable : MeasurableSet rows
  cols_measurable : MeasurableSet cols

structure LatinonBox extends LatinonRectangle where
  symbols : Set I
  symbols_measurable : MeasurableSet symbols
  symbols_interval : Set.OrdConnected symbols

instance : Inhabited LatinonRectangle :=
  ⟨⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty⟩⟩

instance : Inhabited LatinonBox :=
  ⟨{ toLatinonRectangle := default, symbols := Set.univ,
     symbols_measurable := MeasurableSet.univ, symbols_interval := Set.ordConnected_univ }⟩

def LatinonBox.carrier (B : LatinonBox) : Set LatinonPoint := (B.rows ×ˢ B.cols) ×ˢ B.symbols

theorem LatinonBox.measurable (B : LatinonBox) : MeasurableSet B.carrier :=
  (B.rows_measurable.prod B.cols_measurable).prod B.symbols_measurable

def intervalLatinonBox (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (a b : ℝ) : LatinonBox where
  rows := S
  cols := T
  rows_measurable := hS
  cols_measurable := hT
  symbols := unitSymbolInterval a b
  symbols_measurable := unitSymbolInterval_measurable a b
  symbols_interval := Set.ordConnected_Ioc.preimage_mono (fun _ _ h => h)

def cutValueSup {α : Type*} (F : α → ℝ) : ℝ := sSup (Set.range F)

theorem le_cutValueSup {α : Type*} (F : α → ℝ) (hF : ∀ x, F x ≤ 1) (x : α) :
    F x ≤ cutValueSup F :=
  le_csSup ⟨1,by rintro _ ⟨y,rfl⟩; exact hF y⟩ ⟨x,rfl⟩

theorem cutValueSup_le {α : Type*} [Nonempty α] (F : α → ℝ) (c : ℝ)
    (hF : ∀ x, F x ≤ c) : cutValueSup F ≤ c :=
  csSup_le (Set.range_nonempty F) (by rintro _ ⟨x,rfl⟩; exact hF x)

theorem cutValueSup_nonneg {α : Type*} [Nonempty α] (F : α → ℝ)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) : 0 ≤ cutValueSup F := by
  obtain ⟨x⟩ := (inferInstance : Nonempty α)
  exact (hF0 x).trans (le_cutValueSup F hF1 x)

theorem cutValueSup_zero {α : Type*} [Nonempty α] : cutValueSup (fun _ : α => (0 : ℝ)) = 0 :=
  le_antisymm (cutValueSup_le _ 0 (fun _ => le_rfl))
    (cutValueSup_nonneg _ (fun _ => le_rfl) (fun _ => by norm_num))

theorem probability_real_set_bounds {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (S : Set α) :
    0 ≤ mu.real S ∧ mu.real S ≤ 1 :=
  ⟨measureReal_nonneg,(measureReal_mono (Set.subset_univ S)).trans_eq probReal_univ⟩

theorem abs_sub_le_one_of_unit_bounds {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : |a-b| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2]

/-- The distribution cut tests arbitrary measurable row/column sets and
all measurable symbol intervals, not just a fixed finite grid. -/
def measureCut (mu nu : Measure LatinonPoint) : ℝ :=
  cutValueSup (fun B : LatinonBox => |mu.real B.carrier-nu.real B.carrier|)

theorem measureCut_test_le (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (B : LatinonBox) :
    |mu.real B.carrier-nu.real B.carrier| ≤ measureCut mu nu :=
  le_cutValueSup _ (fun B => abs_sub_le_one_of_unit_bounds
    (probability_real_set_bounds mu B.carrier) (probability_real_set_bounds nu B.carrier)) B

theorem measureCut_nonneg (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] : 0 ≤ measureCut mu nu :=
  cutValueSup_nonneg _ (fun _ => abs_nonneg _) (fun B => abs_sub_le_one_of_unit_bounds
    (probability_real_set_bounds mu B.carrier) (probability_real_set_bounds nu B.carrier))

theorem measureCut_le_one (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] : measureCut mu nu ≤ 1 :=
  cutValueSup_le _ 1 (fun B => abs_sub_le_one_of_unit_bounds
    (probability_real_set_bounds mu B.carrier) (probability_real_set_bounds nu B.carrier))

theorem measureCut_self (mu : Measure LatinonPoint) : measureCut mu mu = 0 := by
  simp only [measureCut,sub_self,abs_zero,cutValueSup_zero]

theorem measureCut_symm (mu nu : Measure LatinonPoint) : measureCut mu nu = measureCut nu mu := by
  unfold measureCut
  apply congrArg cutValueSup
  funext B
  exact abs_sub_comm _ _

theorem measureCut_triangle (mu nu xi : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure xi] :
    measureCut mu xi ≤ measureCut mu nu+measureCut nu xi := by
  apply cutValueSup_le
  intro B
  exact (abs_sub_le _ _ _).trans (add_le_add (measureCut_test_le mu nu B) (measureCut_test_le nu xi B))

def orderRelation (f : I → I) : Set (I × I) := {p | f p.1 < f p.2}

def orderBox (f : I → I) (R : LatinonRectangle) : ℝ :=
  ((volume : Measure I).prod volume).real ((R.rows ×ˢ R.cols) ∩ orderRelation f)

def orderCut (f g : I → I) : ℝ :=
  cutValueSup (fun R : LatinonRectangle => |orderBox f R-orderBox g R|)

theorem orderBox_bounds (f : I → I) (R : LatinonRectangle) :
    0 ≤ orderBox f R ∧ orderBox f R ≤ 1 :=
  probability_real_set_bounds _ _

theorem orderCut_test_le (f g : I → I) (R : LatinonRectangle) :
    |orderBox f R-orderBox g R| ≤ orderCut f g :=
  le_cutValueSup _ (fun R => abs_sub_le_one_of_unit_bounds (orderBox_bounds f R) (orderBox_bounds g R)) R

theorem orderCut_nonneg (f g : I → I) : 0 ≤ orderCut f g :=
  cutValueSup_nonneg _ (fun _ => abs_nonneg _)
    (fun R => abs_sub_le_one_of_unit_bounds (orderBox_bounds f R) (orderBox_bounds g R))

theorem orderCut_le_one (f g : I → I) : orderCut f g ≤ 1 :=
  cutValueSup_le _ 1 (fun R => abs_sub_le_one_of_unit_bounds (orderBox_bounds f R) (orderBox_bounds g R))

theorem orderCut_self (f : I → I) : orderCut f f = 0 := by
  simp only [orderCut,sub_self,abs_zero,cutValueSup_zero]

theorem orderCut_symm (f g : I → I) : orderCut f g = orderCut g f := by
  unfold orderCut
  apply congrArg cutValueSup
  funext R
  exact abs_sub_comm _ _

theorem orderCut_triangle (f g h : I → I) : orderCut f h ≤ orderCut f g+orderCut g h := by
  apply cutValueSup_le
  intro R
  exact (abs_sub_le _ _ _).trans (add_le_add (orderCut_test_le f g R) (orderCut_test_le g h R))

theorem orderRelation_measurable (f : I → I) (hf : Measurable f) : MeasurableSet (orderRelation f) :=
  measurableSet_lt (hf.comp measurable_fst) (hf.comp measurable_snd)

/-- The order term uses exactly the source order-fixing bigraphon. -/
theorem orderBox_eq_integral (f : I → I) (hf : Measurable f) (R : LatinonRectangle) :
    orderBox f R = ∫ u in R.rows, ∫ v in R.cols, if f u < f v then (1 : ℝ) else 0 := by
  have hrel := orderRelation_measurable f hf
  have hi : Integrable ((orderRelation f).indicator (fun _ : I × I => (1 : ℝ)))
      ((volume : Measure I).prod volume) := (integrable_const 1).indicator hrel
  calc
    _ = ∫ p in R.rows ×ˢ R.cols, (orderRelation f).indicator (fun _ : I × I => (1 : ℝ)) p
          ∂((volume : Measure I).prod volume) := by
      rw [setIntegral_indicator hrel,setIntegral_const,smul_eq_mul,mul_one]
      rfl
    _ = ∫ u in R.rows, ∫ v in R.cols,
        (orderRelation f).indicator (fun _ : I × I => (1 : ℝ)) (u,v) :=
      setIntegral_prod _ hi.integrableOn
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases h : f u < f v
      · have hm : (u,v) ∈ orderRelation f := h
        rw [Set.indicator_of_mem hm,ite_eq_left h]
      · have hm : (u,v) ∉ orderRelation f := h
        rw [Set.indicator_of_notMem hm,ite_eq_right h]

end LatinonEntropy

#print axioms LatinonEntropy.intervalLatinonBox
#print axioms LatinonEntropy.measureCut_test_le
#print axioms LatinonEntropy.measureCut_nonneg
#print axioms LatinonEntropy.measureCut_le_one
#print axioms LatinonEntropy.measureCut_self
#print axioms LatinonEntropy.measureCut_symm
#print axioms LatinonEntropy.measureCut_triangle
#print axioms LatinonEntropy.orderCut_test_le
#print axioms LatinonEntropy.orderCut_nonneg
#print axioms LatinonEntropy.orderCut_le_one
#print axioms LatinonEntropy.orderCut_self
#print axioms LatinonEntropy.orderCut_symm
#print axioms LatinonEntropy.orderCut_triangle
#print axioms LatinonEntropy.orderBox_eq_integral
