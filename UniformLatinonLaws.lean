module

public import LatinSquareNormalization
public import LatinGridBallLowerBound
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

instance latinArrayFintype (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

instance latinArrayMeasurableSpace (n : ℕ) : MeasurableSpace (LatinArray n) := ⊤

instance latinArrayMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (LatinArray n) :=
  ⟨fun _ => trivial⟩

instance latinonBorelSpace : MeasurableSpace LatinonMeasure := borel LatinonMeasure

instance : BorelSpace LatinonMeasure := ⟨rfl⟩

def cyclicLatinArray (n : ℕ) (hn : 0 < n) : LatinArray n := by
  let _ : NeZero n := ⟨hn.ne'⟩
  exact ⟨fun x y => x+y,fun x => (Equiv.addLeft x).bijective,fun y => (Equiv.addRight y).bijective⟩

theorem allLatinSquares_nonempty (n : ℕ) (hn : 0 < n) : (allLatinSquares n).Nonempty :=
  ⟨cyclicLatinArray n hn,mem_univ _⟩

def uniformLatinSquareMeasure (n : ℕ) : Measure (LatinArray n) :=
  Measure.uniformOfFinset (allLatinSquares n)

theorem uniformLatinSquareMeasure_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (uniformLatinSquareMeasure n) := by
  refine ⟨?_⟩
  rw [uniformLatinSquareMeasure,Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ,filter_true]
  exact ENNReal.div_self (by exact_mod_cast (card_pos.mpr (allLatinSquares_nonempty n hn)).ne') (by simp)

def uniformLatinonLaw {n : ℕ} (hn : 0 < n) : Measure LatinonMeasure :=
  (uniformLatinSquareMeasure n).map (latinArrayToLatinonMeasure hn)

theorem finite_latinon_embedding_measurable {n : ℕ} (hn : 0 < n) :
    Measurable (latinArrayToLatinonMeasure hn) := measurable_of_countable _

instance uniformLatinonLaw_probability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (uniformLatinonLaw hn) := by
  let _ := uniformLatinSquareMeasure_probability n hn
  refine ⟨?_⟩
  rw [uniformLatinonLaw,Measure.map_apply (finite_latinon_embedding_measurable hn) MeasurableSet.univ]
  simp only [Set.preimage_univ,measure_univ]

def latinonEventLatinFamily {n : ℕ} (hn : 0 < n) (B : Set LatinonMeasure) : Finset (LatinArray n) :=
  (allLatinSquares n).filter (fun L => latinArrayToLatinonMeasure hn L ∈ B)

theorem uniformLatinonLaw_event {n : ℕ} (hn : 0 < n) (B : Set LatinonMeasure) (hB : MeasurableSet B) :
    uniformLatinonLaw hn B = (latinonEventLatinFamily hn B).card/(allLatinSquares n).card := by
  rw [uniformLatinonLaw,Measure.map_apply (finite_latinon_embedding_measurable hn) hB,
    uniformLatinSquareMeasure,Measure.uniformOfFinset_apply]
  rfl

theorem uniformLatinonLaw_real_event {n : ℕ} (hn : 0 < n) (B : Set LatinonMeasure) (hB : MeasurableSet B) :
    (uniformLatinonLaw hn).real B = ((latinonEventLatinFamily hn B).card : ℝ)/(allLatinSquares n).card := by
  rw [measureReal_def,uniformLatinonLaw_event hn B hB,ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]

theorem uniformLatinonLaw_real_ball {n : ℕ} (hn : 0 < n) (W : LatinonMeasure) (rho : ℝ) :
    (uniformLatinonLaw hn).real (Metric.ball W rho) =
      ((latinonBallLatinFamily hn W rho).card : ℝ)/(allLatinSquares n).card := by
  exact uniformLatinonLaw_real_event hn _ Metric.isOpen_ball.measurableSet

end LatinonEntropy

#print axioms LatinonEntropy.cyclicLatinArray
#print axioms LatinonEntropy.allLatinSquares_nonempty
#print axioms LatinonEntropy.uniformLatinSquareMeasure_probability
#print axioms LatinonEntropy.finite_latinon_embedding_measurable
#print axioms LatinonEntropy.uniformLatinonLaw_probability
#print axioms LatinonEntropy.uniformLatinonLaw_event
#print axioms LatinonEntropy.uniformLatinonLaw_real_event
#print axioms LatinonEntropy.uniformLatinonLaw_real_ball
