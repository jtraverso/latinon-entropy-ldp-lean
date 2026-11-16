/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. Released under Apache-2.0.
-/
module
public import Mathlib

/-!
# Entropy and large deviations for Latin squares

This statement interface uses only Mathlib. All mathematical definitions are
copied from the published Lean development, with the same names and values.
The uniform finite law, full ordered cut pseudometric, relative entropy and
strict order-pattern sampling are defined explicitly below. The three metric
identities and three embedding-margin identities are compared auxiliary claims:
their intentional holes do not occur in the Solution or its import closure.

The principal claims are the closed/open LDP bounds at speed n^2, goodness of
the extended KL rate, finite-rate pattern counting with binomial normalization,
eventual emptiness of infeasible pattern neighborhoods, the uniform finite
tensor lower bound, and transportation correction with coefficient 5/2.
Pattern radii depend on the target and are chosen before the order threshold.
Entropy is -KL. The transportation improvement is not claimed to be optimal.
The manuscript identifies the model with GHHS and explains the sign convention
in its comparison with Conjecture 12.4 (arXiv v3). CDR applications are present
in the source development but are not separate claims in this configuration.
-/

@[expose] public section
noncomputable section
namespace LatinonEntropy
open MeasureTheory ProbabilityTheory Finset
open scoped Classical ENNReal unitInterval

/-- Rows, columns and symbols in the unit interval. -/
abbrev LatinonPoint := (I × I) × I

/-- A cube measure with uniform pair marginals and one measure-preserving order map. -/
structure LatinonMeasure where
  measure : Measure LatinonPoint
  order : I → I
  order_preserving : MeasurePreserving order volume volume
  xy_uniform : ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
    measure ((S ×ˢ T) ×ˢ Set.univ) = volume S * volume T
  xz_uniform : ∀ (S U : Set I), MeasurableSet S → MeasurableSet U →
    measure ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U
  yz_uniform : ∀ (T U : Set I), MeasurableSet T → MeasurableSet U →
    measure ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U

instance (W : LatinonMeasure) : IsProbabilityMeasure W.measure where
  measure_univ := by
    have h := W.xy_uniform Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa only [Set.univ_prod_univ,measure_univ,mul_one] using h

/-- Uniform cube measure with identity order. -/
def uniformLatinonMeasure : LatinonMeasure where
  measure := ((volume : Measure I).prod volume).prod volume
  order := id
  order_preserving := MeasurePreserving.id volume
  xy_uniform := by
    intro S T _ _
    simp only [Measure.prod_prod,measure_univ,mul_one]
  xz_uniform := by
    intro S U _ _
    simp only [Measure.prod_prod,measure_univ,mul_one]
  yz_uniform := by
    intro T U _ _
    simp only [Measure.prod_prod,measure_univ,one_mul]

/-- A measurable, measure-preserving bijection of the unit interval. -/
structure LatinonRelabel where
  equiv : I ≃ᵐ I
  preserves : MeasurePreserving equiv volume volume

instance : CoeFun LatinonRelabel (fun _ => I → I) := ⟨fun e => e.equiv⟩

namespace LatinonRelabel

/-- Identity relabeling. -/
def refl : LatinonRelabel := ⟨MeasurableEquiv.refl I,MeasurePreserving.id volume⟩

/-- Inverse measurable relabeling. -/
def symm (e : LatinonRelabel) : LatinonRelabel :=
  ⟨e.equiv.symm,MeasurePreserving.symm e.equiv e.preserves⟩

end LatinonRelabel

/-- Inverse row/column coordinate map; symbols retain their order. -/
def inverseCoordinateRelabel (e f : LatinonRelabel) (p : LatinonPoint) : LatinonPoint :=
  ((e.symm p.1.1,f.symm p.1.2),p.2)

/-- Pushforward along the inverse coordinate relabeling. -/
def relabelLatinonMeasure (mu : Measure LatinonPoint) (e f : LatinonRelabel) : Measure LatinonPoint :=
  mu.map (inverseCoordinateRelabel e f)

/-- Measurable row and column test sets. -/
structure LatinonRectangle where
  rows : Set I
  cols : Set I
  rows_measurable : MeasurableSet rows
  cols_measurable : MeasurableSet cols

/-- A measurable rectangle together with a measurable symbol interval. -/
structure LatinonBox extends LatinonRectangle where
  symbols : Set I
  symbols_measurable : MeasurableSet symbols
  symbols_interval : Set.OrdConnected symbols

/-- The corresponding product test set in the cube. -/
def LatinonBox.carrier (B : LatinonBox) : Set LatinonPoint := (B.rows ×ˢ B.cols) ×ˢ B.symbols

/-- Supremum over the specified cut tests. -/
def cutValueSup {α : Type*} (F : α → ℝ) : ℝ := sSup (Set.range F)

/-- Distribution cut norm over row/column sets and symbol intervals. -/
def measureCut (mu nu : Measure LatinonPoint) : ℝ :=
  cutValueSup (fun B : LatinonBox => |mu.real B.carrier-nu.real B.carrier|)

/-- Strict order relation induced by the order map. -/
def orderRelation (f : I → I) : Set (I × I) := {p | f p.1 < f p.2}

/-- Order mass tested on a measurable rectangle. -/
def orderBox (f : I → I) (R : LatinonRectangle) : ℝ :=
  ((volume : Measure I).prod volume).real ((R.rows ×ˢ R.cols) ∩ orderRelation f)

/-- Cut norm of the difference of two order relations. -/
def orderCut (f g : I → I) : ℝ :=
  cutValueSup (fun R : LatinonRectangle => |orderBox f R-orderBox g R|)

/-- Two order terms plus the distribution cut term. -/
def latinonAlignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) : ℝ :=
  orderCut W.order (V.order ∘ e)+orderCut W.order (V.order ∘ f)+
    measureCut W.measure (relabelLatinonMeasure V.measure e f)

/-- Infimum of alignment costs over independent row/column bijections. -/
def latinonCutDistance (W V : LatinonMeasure) : ℝ :=
  sInf (Set.range (fun p : LatinonRelabel × LatinonRelabel => latinonAlignmentCost W V p.1 p.2))

/-- The full cut distance vanishes on the diagonal (auxiliary comparison). -/
theorem latinonCutDistance_self (W : LatinonMeasure) : latinonCutDistance W W = 0 := by
  sorry

/-- Symmetry of the full cut distance (auxiliary comparison). -/
theorem latinonCutDistance_symm (W V : LatinonMeasure) : latinonCutDistance W V = latinonCutDistance V W := by
  sorry

/-- Triangle inequality (auxiliary comparison). -/
theorem latinonCutDistance_triangle (W V U : LatinonMeasure) :
    latinonCutDistance W U ≤ latinonCutDistance W V+latinonCutDistance V U := by
  sorry

instance : PseudoMetricSpace LatinonMeasure where
  dist := latinonCutDistance
  dist_self := latinonCutDistance_self
  dist_comm := latinonCutDistance_symm
  dist_triangle := latinonCutDistance_triangle

/-- Extended KL divergence from uniform cube volume, including singular measures. -/
def latinonRate (W : LatinonMeasure) : ℝ≥0∞ :=
  InformationTheory.klDiv W.measure uniformLatinonMeasure.measure

/-- An array whose rows and columns are bijections. -/
def LatinArray (n : ℕ) := {L : Fin n → Fin n → Fin n //
  (∀ x, Function.Bijective (L x)) ∧ (∀ y, Function.Bijective (fun x => L x y))}

instance latinArrayFintype (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

/-- Equal-width symbol-grid data. -/
def symbolGridLower {n : ℕ} (z : Fin n) : ℝ := (z.val : ℝ)/(n : ℝ)

/-- Equal-width symbol-grid data. -/
def symbolGridUpper {n : ℕ} (z : Fin n) : ℝ := ((z.val : ℝ)+1)/(n : ℝ)

/-- Equal-width symbol-grid data. -/
def symbolGridCell {n : ℕ} (z : Fin n) : Set ℝ := Set.Ioc (symbolGridLower z) (symbolGridUpper z)

/-- Preimage of a symbol-grid cell in the unit interval. -/
def lebesgueGridCell {n : ℕ} (z : Fin n) : Set I :=
  ((↑) : I → ℝ) ⁻¹' symbolGridCell z

/-- Grid embedding: n times the sum of uniform product measures on occupied cells. -/
def finiteLatinMeasure {n : ℕ} (L : LatinArray n) : Measure ((I × I) × I) :=
  (n : NNReal) • ∑ x, ∑ y,
    (((volume : Measure I).restrict (lebesgueGridCell x)).prod
      (volume.restrict (lebesgueGridCell y))).prod
        (volume.restrict (lebesgueGridCell (L.val x y)))

/-- Uniform row/column marginal of the grid embedding. Auxiliary comparison. -/
theorem finiteLatinMeasure_xy {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    finiteLatinMeasure L ((S ×ˢ T) ×ˢ Set.univ) = volume S*volume T := by
  sorry

/-- Uniform row/symbol marginal of the grid embedding. Auxiliary comparison. -/
theorem finiteLatinMeasure_xz {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S U : Set I)
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    finiteLatinMeasure L ((S ×ˢ Set.univ) ×ˢ U) = volume S*volume U := by
  sorry

/-- Uniform column/symbol marginal of the grid embedding. Auxiliary comparison. -/
theorem finiteLatinMeasure_yz {n : ℕ} (hn : 0 < n) (L : LatinArray n) (T U : Set I)
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    finiteLatinMeasure L ((Set.univ ×ˢ T) ×ˢ U) = volume T*volume U := by
  sorry

/-- The finite square as a Latinon with identity order. -/
def latinArrayToLatinonMeasure {n : ℕ} (hn : 0 < n) (L : LatinArray n) : LatinonMeasure where
  measure := finiteLatinMeasure L
  order := id
  order_preserving := MeasurePreserving.id volume
  xy_uniform := finiteLatinMeasure_xy hn L
  xz_uniform := finiteLatinMeasure_xz hn L
  yz_uniform := finiteLatinMeasure_yz hn L

/-- The finite set of all labeled Latin squares of a given order. -/
def allLatinSquares (n : ℕ) : Finset (LatinArray n) := univ

instance latinArrayMeasurableSpace (n : ℕ) : MeasurableSpace (LatinArray n) := ⊤

instance latinArrayMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (LatinArray n) :=
  ⟨fun _ => trivial⟩

instance latinonBorelSpace : MeasurableSpace LatinonMeasure := borel LatinonMeasure

/-- Uniform measure on the finite set of labeled Latin squares. -/
def uniformLatinSquareMeasure (n : ℕ) : Measure (LatinArray n) :=
  Measure.uniformOfFinset (allLatinSquares n)

/-- Pushforward of the actual uniform finite-square law under the grid embedding. -/
def uniformLatinonLaw {n : ℕ} (hn : 0 < n) : Measure LatinonMeasure :=
  (uniformLatinSquareMeasure n).map (latinArrayToLatinonMeasure hn)

/-- Lower semicontinuity of the extended KL rate in the full cut topology. -/
theorem latinon_rate_lowerSemicontinuous : LowerSemicontinuous latinonRate := by
  sorry

/-- Compactness of the full ordered Latinon space. -/
theorem latinon_full_cut_compact : IsCompact (Set.univ : Set LatinonMeasure) := by
  sorry

/-- Compactness of every extended-rate sublevel. -/
theorem latinon_rate_sublevels_compact (r : ℝ≥0∞) : IsCompact {W : LatinonMeasure | latinonRate W ≤ r} := by
  sorry

/-- Theorem 2.1: global closed-set upper LDP bound, with nonstrict extended-rate floor. -/
theorem closed_uniform_latinon_upper (F : Set LatinonMeasure) (hF : IsClosed F)
    (t : ℝ) (ht : ∀ W ∈ F, ENNReal.ofReal t ≤ latinonRate W) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real F ≤ Real.exp ((n : ℝ)^2*(-t+eps)) := by
  sorry

/-- Theorem 2.1: global open-set lower LDP bound with a finite-rate witness. -/
theorem open_uniform_latinon_lower (G : Set LatinonMeasure) (hG : IsOpen G)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : ∃ W ∈ G, latinonRate W ≤ ENNReal.ofReal t)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (-(n : ℝ)^2*(t+eps)) ≤ (uniformLatinonLaw (hN.trans_le hn)).real G := by
  sorry

/-- A rectangular order pattern uses each strict rank once. -/
abbrev LatinOrderPattern (k l : ℕ) := (Fin k × Fin l) ≃ Fin (k*l)

/-- Vectors realizing all strict rank comparisons of the pattern. -/
def orderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → ℝ) :=
  {v | ∀ a b, P a < P b → v a < v b}

/-- Canonical conditional symbol kernel obtained by disintegration of the cube measure. -/
def latinonSymbolKernel (W : LatinonMeasure) : Kernel (I × I) I := W.measure.condKernel

instance latinonSymbolKernel_markov (W : LatinonMeasure) : IsMarkovKernel (latinonSymbolKernel W) := by
  unfold latinonSymbolKernel
  infer_instance

/-- Finite conditional product of Markov kernels. -/
def finiteIndependentKernel {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] : Kernel A (∀ j, B j) where
  toFun a := Measure.pi (fun j => K j a)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨S,hS,rfl⟩
    have hSm : ∀ j, MeasurableSet (S j) := fun j => hS j (Set.mem_univ j)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_fun_prod _ (fun j _ => (K j).measurable_coe (hSm j))

theorem finiteIndependentKernel_apply {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] (a : A) :
    finiteIndependentKernel K a=Measure.pi (fun j => K j a) := rfl

instance finiteIndependentKernel_markov {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] :
    IsMarkovKernel (finiteIndependentKernel K) :=
  ⟨fun a => by rw [finiteIndependentKernel_apply]; infer_instance⟩

/-- Sampled row and column coordinates. -/
abbrev LatinonPatternConfig (k l : ℕ) := (Fin k → I) × (Fin l → I)

/-- Independent uniform row and column samples. -/
def latinonPatternConfigLaw (k l : ℕ) : Measure (LatinonPatternConfig k l) :=
  (Measure.pi (fun _ : Fin k => (volume : Measure I))).prod
    (Measure.pi (fun _ : Fin l => (volume : Measure I)))

instance latinonPatternConfigLaw_probability (k l : ℕ) :
    IsProbabilityMeasure (latinonPatternConfigLaw k l) := by
  unfold latinonPatternConfigLaw
  infer_instance

/-- Configurations ordered by the common order map. -/
def orderedLatinonPatternConfigs (W : LatinonMeasure) (k l : ℕ) :
    Set (LatinonPatternConfig k l) :=
  {c | StrictMono (W.order ∘ c.1) ∧ StrictMono (W.order ∘ c.2)}

/-- Conditional symbol kernel for one sampled cell. -/
def latinonPatternCellKernel (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    Kernel (LatinonPatternConfig k l) I :=
  (latinonSymbolKernel W).comap (fun c => (c.1 a.1,c.2 a.2))
    (((measurable_pi_apply a.1).comp measurable_fst).prodMk
      ((measurable_pi_apply a.2).comp measurable_snd))

instance latinonPatternCellKernel_markov (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    IsMarkovKernel (latinonPatternCellKernel W k l a) := by
  unfold latinonPatternCellKernel
  infer_instance

/-- Conditional independent symbol samples over all cells. -/
def latinonPatternSymbolKernel (W : LatinonMeasure) (k l : ℕ) :
    Kernel (LatinonPatternConfig k l) ((Fin k × Fin l) → I) :=
  finiteIndependentKernel (latinonPatternCellKernel W k l)

instance latinonPatternSymbolKernel_markov (W : LatinonMeasure) (k l : ℕ) :
    IsMarkovKernel (latinonPatternSymbolKernel W k l) := by
  unfold latinonPatternSymbolKernel
  infer_instance

/-- Strict pattern realizations with values in the unit interval. -/
def unitOrderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → I) :=
  (fun v a => (v a : ℝ)) ⁻¹' orderPatternRealizations P

/-- Joint coordinate and conditional-symbol law. -/
def latinonPatternSampleLaw (W : LatinonMeasure) (k l : ℕ) :
    Measure (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  latinonPatternConfigLaw k l ⊗ₘ latinonPatternSymbolKernel W k l

instance latinonPatternSampleLaw_probability (W : LatinonMeasure) (k l : ℕ) :
    IsProbabilityMeasure (latinonPatternSampleLaw W k l) := by
  unfold latinonPatternSampleLaw
  infer_instance

/-- Ordered configurations whose sampled symbols realize the specified pattern. -/
def latinonPatternEvent {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) :
    Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  orderedLatinonPatternConfigs W k l ×ˢ unitOrderPatternRealizations P

/-- Factorial-normalized ordered-sampling probability. -/
def latinonPatternDensity {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real (latinonPatternEvent W P)

/-- Vector of pattern densities of the actual Latinon. -/
def latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (W : LatinonMeasure) : J → ℝ :=
  fun j => latinonPatternDensity W (P j)

/-- Finite row and column index selections. -/
abbrev FinitePatternConfig (n k l : ℕ) := (Fin k → Fin n) × (Fin l → Fin n)

/-- Increasing index selections realizing the strict order pattern. -/
def finiteMatrixPatternConfigs {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (FinitePatternConfig n k l) :=
  {c | StrictMono c.1 ∧ StrictMono c.2 ∧ ∀ a b, P a < P b →
    L.val (c.1 a.1) (c.2 a.2) < L.val (c.1 b.1) (c.2 b.2)}

/-- Finite set of those increasing index selections. -/
def finiteMatrixPatternFamily {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Finset (FinitePatternConfig n k l) := Finset.univ.filter (fun c => c ∈ finiteMatrixPatternConfigs L P)

/-- Finite count divided by the product of the two binomial coefficients. -/
def standardMatrixPatternDensity {n k l : ℕ} (L : LatinArray n)
    (P : LatinOrderPattern k l) : ℝ :=
  ((finiteMatrixPatternFamily L P).card : ℝ)/
    ((n.choose k : ℝ)*(n.choose l : ℝ))

/-- Vector of finite binomial-normalized densities. -/
def standardMatrixPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (L : LatinArray n) : J → ℝ :=
  fun j => standardMatrixPatternDensity L (P j)

/-- Labeled Latin squares whose finite pattern vector lies in the chosen closed box. -/
def standardMatrixPatternBoxFamily {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ) (rho : ℝ) (n : ℕ)
    [Fintype J] : Finset (LatinArray n) :=
  (allLatinSquares n).filter (fun L => standardMatrixPatternProfile P L ∈ Metric.closedBall z rho)

/-- Infimum of extended KL divergence over the exact compatible Latinon fiber. -/
def latinonContractedRate {Y : Type*} (T : LatinonMeasure → Y) (z : Y) : ℝ≥0∞ :=
  ⨅ W : {W : LatinonMeasure // T W=z}, latinonRate W.1

/-- Theorem 2.2: bilateral logarithmic count for finite-rate targets; radius depends on the target and precedes n. -/
theorem finite_rate_standard_pattern_log_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      0 < (standardMatrixPatternBoxFamily P z rho n).card ∧
      |Real.log ((standardMatrixPatternBoxFamily P z rho n).card : ℝ)/(n : ℝ)^2-
        (Real.log (n : ℝ)-2)+(latinonContractedRate (latinonPatternProfile P) z).toReal| ≤ eta := by
  sorry

/-- Empty Latinon fibers have eventually empty finite neighborhoods. -/
theorem empty_standard_pattern_fiber_eventually_zero {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hempty : ¬∃ W : LatinonMeasure, latinonPatternProfile P W=z)
    (r : ℝ) (hr : 0 < r) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n), (standardMatrixPatternBoxFamily P z rho n).card=0 := by
  sorry

/-- Finite squares satisfying every three-coordinate subset-cut tolerance. -/
def latinTensorCutFamily {n : ℕ} (p : Fin n → Fin n → Fin n → ℝ) (rho : ℝ) :
    Finset (LatinArray n) :=
  univ.filter (fun L => ∀ «I» U V : Finset (Fin n),
    |∑ x ∈ «I», ∑ i ∈ U, ∑ j ∈ V, ((if L.val x i = j then (1 : ℝ) else 0)-p x i j)| ≤
      rho*(n : ℝ)^2)

/-- Theorem 3.1: a common order threshold for all bounded positive tristochastic profiles. -/
theorem finite_latin_tensor_lower_bound (a b rho eta : ℝ) (ha : 0 < a)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ p : Fin n → Fin n → Fin n → ℝ,
      (∀ x i j, a/(n : ℝ) ≤ p x i j ∧ p x i j ≤ b/(n : ℝ)) →
      (∀ x i, ∑ j, p x i j = 1) →
      (∀ x j, ∑ i, p x i j = 1) →
      (∀ i j, ∑ x, p x i j = 1) →
      (latinTensorCutFamily p rho).Nonempty ∧
      Real.exp (-(∑ x, ∑ i, ∑ j, p x i j*Real.log (p x i j))-
        (2+eta)*(n : ℝ)^2) ≤ (latinTensorCutFamily p rho).card := by
  sorry

/-- Sum of matrix entries on a rectangular cut. -/
def rectMass {n : ℕ} (B : Fin n → Fin n → ℝ) (S T : Finset (Fin n)) : ℝ :=
  ∑ y ∈ S, ∑ z ∈ T, B y z

/-- The proved refinement of Lemma 4.1: exact support, entry bounds and l1 cost at most 5/2 times the margin defect. -/
theorem correction_lemma_five
    {n : ℕ} (hn : 0 < n) (eps rho a c d : ℝ)
    (heps : 0 < eps) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (ha : 0 < a) (hac : a ≤ c)
    (A M : Fin n → Fin n → ℝ)
    (hA : ∀ y z, A y z = 0 ∨ A y z = 1)
    (hrowA : ∀ y, (∑ z, A y z) = d) (hcolA : ∀ z, (∑ y, A y z) = d)
    (hdegree : eps * n ≤ d)
    (hcut : ∀ S T : Finset (Fin n),
      rho * S.card * T.card - rho * eps * (n : ℝ)^2 /
        (64 * max c (16 / (rho * eps))) ≤ rectMass A S T)
    (hzero : ∀ y z, A y z = 0 → M y z = 0)
    (hM : ∀ y z, A y z = 1 → a / n ≤ M y z ∧ M y z ≤ c / n) :
    ∃ Q : Fin n → Fin n → ℝ,
      (∀ y, ∑ z, Q y z = 1) ∧ (∀ z, ∑ y, Q y z = 1) ∧
      (∀ y z, 0 ≤ Q y z) ∧
      (∀ y z, A y z = 0 → Q y z = 0) ∧
      (∀ y z, A y z = 1 → min (a/2) (1/4) / n ≤ Q y z ∧
        Q y z ≤ max c (16 / (rho * eps)) / n) ∧
      (∑ y, ∑ z, |Q y z - M y z|) ≤
        (5 / 2 : ℝ) * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  sorry

end LatinonEntropy
