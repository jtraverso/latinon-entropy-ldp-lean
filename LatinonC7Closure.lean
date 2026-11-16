module

public import LatinonSymbolKernelCompression
public import KernelGraphAEBounds
public import LatinonPatternSampling
public import LatinonKernelFamily
public import LebesgueGridPartition
public import LatinonPatternNormalization
public import LatinonPseudometric
public import GridCoordinateIndex
public import FiniteLatinMeasureMargins
public import LatinonBridge.LocalObservableEntropy

@[expose] public section

-- Source: LatinonSymbolAverages.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonSymbolKernel_real_mem_Icc (W : LatinonMeasure) (U : Set I) (p : I × I) :
    (latinonSymbolKernel W p).real U ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  exact measureReal_le_one

/-- Each conditional symbol event has the prescribed uniform mean in
almost every row. This uses the xz marginal, including for singular W. -/
theorem latinonSymbolKernel_row_mean (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    (fun x => ∫ y, (latinonSymbolKernel W (x,y)).real U ∂volume)=ᵐ[volume]
      (fun _ : I => (volume : Measure I).real U) := by
  have hi := integrable_real_latinonSymbolKernel_event W U hU
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi.integral_prod_left (integrable_const _)
  intro S hS _
  have he := setIntegral_prod (fun p => (latinonSymbolKernel W p).real U)
    (s := S) (t := Set.univ) hi.integrableOn
  simp only [Measure.restrict_univ] at he
  rw [← he,latinonSymbolKernel_real_rectangle W S Set.univ U hS MeasurableSet.univ hU,
    W.xz_uniform_real S U hS hU,setIntegral_const,smul_eq_mul]

/-- The corresponding column identity follows from the yz marginal. -/
theorem latinonSymbolKernel_col_mean (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    (fun y => ∫ x, (latinonSymbolKernel W (x,y)).real U ∂volume)=ᵐ[volume]
      (fun _ : I => (volume : Measure I).real U) := by
  have hi := integrable_real_latinonSymbolKernel_event W U hU
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi.integral_prod_right (integrable_const _)
  intro T hT _
  have he := setIntegral_prod (fun p : I × I => (latinonSymbolKernel W p.swap).real U)
    (s := T) (t := Set.univ) hi.swap.integrableOn
  simp only [Measure.restrict_univ,Prod.swap_prod_mk] at he
  rw [← he,setIntegral_prod_swap Set.univ T (fun p => (latinonSymbolKernel W p).real U),
    latinonSymbolKernel_real_rectangle W Set.univ T U MeasurableSet.univ hT hU,
    W.yz_uniform_real T U hT hU,setIntegral_const,smul_eq_mul]

theorem latinonSymbolKernel_mean (W : LatinonMeasure) (U : Set I) (hU : MeasurableSet U) :
    (∫ p, (latinonSymbolKernel W p).real U ∂unitSquareVolume)=(volume : Measure I).real U := by
  rw [integral_prod _ (integrable_real_latinonSymbolKernel_event W U hU),
    integral_congr_ae (latinonSymbolKernel_row_mean W U hU)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

end LatinonEntropy

end

-- Source: VertexLeafIntegration.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

theorem integral_resampleCoordinate {V : Type*} [Fintype V] [DecidableEq V]
    (u : V) (f : (V → I) → ℝ) (hf : Integrable f (vertexSampleLaw V)) :
    (∫ x, f x ∂vertexSampleLaw V)=
      ∫ x, ∫ t, f (resampleCoordinate u (x,t)) ∂volume ∂vertexSampleLaw V := by
  have hm := resampleCoordinate_preserving u
  have hfmap : AEStronglyMeasurable f
      (Measure.map (resampleCoordinate u) ((vertexSampleLaw V).prod volume)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hfmap
  rw [hm.map_eq] at he
  exact he.trans (integral_prod _ (hm.integrable_comp_of_integrable hf))

theorem integral_vertexPair {V : Type*} [Fintype V] (u v : V) (huv : u ≠ v)
    (f : I × I → ℝ) (hf : Integrable f unitSquareVolume) :
    (∫ x, f (x u,x v) ∂vertexSampleLaw V)=∫ p, f p ∂unitSquareVolume := by
  have hm := vertexPair_preserving u v huv
  have hfmap : AEStronglyMeasurable f (Measure.map (fun x : V → I => (x u,x v)) (vertexSampleLaw V)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hfmap
  rw [hm.map_eq] at he
  exact he.symm

/-- A leaf coordinate can be integrated out using an a.e. constant kernel
margin. The other factor may share the leaf's other endpoint. -/
theorem integral_vertex_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (u v r s : V) (huv : u ≠ v) (hru : r ≠ u) (hsu : s ≠ u)
    (f g : I × I → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (hgb : ∀ p, g p ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hmean : (fun y => ∫ t, f (t,y) ∂volume)=ᵐ[volume] (fun _ : I => c)) :
    (∫ x, f (x u,x v)*g (x r,x s) ∂vertexSampleLaw V)=
      c*(∫ x, g (x r,x s) ∂vertexSampleLaw V) := by
  let F : (V → I) → ℝ := fun x => f (x u,x v)*g (x r,x s)
  have hFi : Integrable F (vertexSampleLaw V) := by
    apply Integrable.of_mem_Icc 0 1
      ((hfm.comp ((measurable_pi_apply u).prodMk (measurable_pi_apply v))).mul
        (hgm.comp ((measurable_pi_apply r).prodMk (measurable_pi_apply s)))).aemeasurable
    apply ae_of_all
    intro x
    exact ⟨mul_nonneg (hfb _).1 (hgb _).1,
      (mul_le_mul_of_nonneg_right (hfb _).2 (hgb _).1).trans
        (by simpa only [one_mul] using (hgb _).2)⟩
  have hm := (measurePreserving_eval (fun _ : V => (volume : Measure I)) v).quasiMeasurePreserving.ae hmean
  have hpoint (x : V → I) (t : I) :
      F (resampleCoordinate u (x,t))=f (t,x v)*g (x r,x s) := by
    simp only [F,resampleCoordinate,update_self,update_of_ne huv.symm,
      update_of_ne hru,update_of_ne hsu]
  calc
    _ = ∫ x, ∫ t, F (resampleCoordinate u (x,t)) ∂volume ∂vertexSampleLaw V :=
      integral_resampleCoordinate u F hFi
    _ = ∫ x, c*g (x r,x s) ∂vertexSampleLaw V := by
      apply integral_congr_ae
      filter_upwards [hm] with x hx
      simp_rw [hpoint,integral_mul_const]
      rw [hx]
    _ = _ := integral_const_mul _ _

end LatinonEntropy

end

-- Source: LatinonPatternGraph.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev PatternVertex (k l : ℕ) := Fin k ⊕ Fin l

abbrev patternGraphEdge {k l : ℕ} (e : PatternVertex k l × PatternVertex k l) : Prop :=
  match e.1,e.2 with
  | .inl i,.inl j => i < j
  | .inr i,.inr j => i < j
  | .inl _,.inr _ => True
  | .inr _,.inl _ => False

def patternGraphEdges (k l : ℕ) : Finset (PatternVertex k l × PatternVertex k l) :=
  Finset.univ.filter patternGraphEdge

theorem patternGraphEdges_noOpposite (k l : ℕ) : NoOppositeEdges (patternGraphEdges k l) := by
  rintro ⟨u,v⟩ he hs
  simp only [patternGraphEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he hs
  cases u <;> cases v <;> simp_all [patternGraphEdge,Prod.swap] <;> omega

def patternEdgeKernel {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ)
    (e : PatternVertex k l × PatternVertex k l) : I × I → ℝ :=
  match e.1,e.2 with
  | .inl _,.inl _ => A
  | .inr _,.inr _ => B
  | .inl i,.inr j => K (i,j)
  | .inr _,.inl _ => fun _ => 1

def strictPairProduct {n : ℕ} (A : I × I → ℝ) (x : Fin n → I) : ℝ :=
  ∏ i, ∏ j, if i < j then A (x i,x j) else 1

theorem patternGraphProduct_factor {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ) (x : PatternVertex k l → I) :
    kernelGraphProduct (patternGraphEdges k l) (patternEdgeKernel A B K) x=
      strictPairProduct A (x ∘ Sum.inl)*strictPairProduct B (x ∘ Sum.inr)*
        ∏ a : Fin k × Fin l, K a (x (.inl a.1),x (.inr a.2)) := by
  unfold kernelGraphProduct patternGraphEdges strictPairProduct
  rw [Finset.prod_filter,Fintype.prod_prod_type,Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type,patternGraphEdge,patternEdgeKernel,
    Finset.prod_mul_distrib,Fintype.prod_prod_type,Function.comp_apply]
  simp only [ite_true,ite_false,Finset.prod_const_one,one_mul]
  ring

theorem patternEdgeKernel_measurable {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hK : ∀ a, Measurable (K a)) (e : PatternVertex k l × PatternVertex k l) :
    Measurable (patternEdgeKernel A B K e) := by
  obtain ⟨u,v⟩ := e
  cases u <;> cases v
  · exact hA
  · exact hK _
  · exact measurable_const
  · exact hB

theorem patternEdgeKernel_bounds {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ)
    (hA : ∀ᵐ p ∂unitSquareVolume, A p ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ᵐ p ∂unitSquareVolume, B p ∈ Set.Icc (0 : ℝ) 1)
    (hK : ∀ a, ∀ᵐ p ∂unitSquareVolume, K a p ∈ Set.Icc (0 : ℝ) 1)
    (e : PatternVertex k l × PatternVertex k l) :
    ∀ᵐ p ∂unitSquareVolume, patternEdgeKernel A B K e p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨u,v⟩ := e
  cases u <;> cases v
  · exact hA
  · exact hK _
  · exact ae_of_all _ (fun _ => ⟨zero_le_one,le_refl 1⟩)
  · exact hB

theorem strictPairProduct_order (W : LatinonMeasure) {n : ℕ} (x : Fin n → I) :
    strictPairProduct (latinonOrderKernel W) x=
      if StrictMono (W.order ∘ x) then (1 : ℝ) else 0 := by
  unfold strictPairProduct
  by_cases h : StrictMono (W.order ∘ x)
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j _
    by_cases hij : i < j
    · rw [ite_eq_left hij]
      have hm : (x i,x j) ∈ orderRelation W.order := h hij
      exact Set.indicator_of_mem hm _
    · exact ite_eq_right hij
  · rw [ite_eq_right h]
    simp only [StrictMono,Function.comp_apply,not_forall] at h
    obtain ⟨i,j,hij,hn⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [ite_eq_left hij]
    have hm : (x i,x j) ∉ orderRelation W.order := hn
    exact Set.indicator_of_notMem hm _

def patternConfigVertices {k l : ℕ} (c : LatinonPatternConfig k l) : PatternVertex k l → I :=
  Sum.elim c.1 c.2

theorem patternConfigVertices_preserving (k l : ℕ) :
    MeasurePreserving (patternConfigVertices (k := k) (l := l))
      (latinonPatternConfigLaw k l) (vertexSampleLaw (PatternVertex k l)) :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ : PatternVertex k l => (volume : Measure I))

end LatinonEntropy

end

-- Source: LatinonCoarsePatterns.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def patternBinAssignments {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    Finset ((Fin k × Fin l) → Fin q) :=
  Finset.univ.filter (fun b => ∀ a c, P a < P c → b a < b c)

def patternBinRectangle {k l q : ℕ} (b : (Fin k × Fin l) → Fin q) :
    Set ((Fin k × Fin l) → I) := Set.pi Set.univ (fun a => lebesgueGridCell (b a))

def coarsePatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    Set ((Fin k × Fin l) → I) := ⋃ b ∈ patternBinAssignments P q, patternBinRectangle b

def symbolGridCollision (k l q : ℕ) : Set ((Fin k × Fin l) → I) :=
  {z | ∃ a b, a ≠ b ∧ ∃ j : Fin q, z a ∈ lebesgueGridCell j ∧ z b ∈ lebesgueGridCell j}

theorem measurableSet_patternBinRectangle {k l q : ℕ} (b : (Fin k × Fin l) → Fin q) :
    MeasurableSet (patternBinRectangle b) :=
  MeasurableSet.univ_pi (fun a => lebesgueGridCell_measurable (b a))

theorem measurableSet_coarsePatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    MeasurableSet (coarsePatternRealizations P q) :=
  MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ => measurableSet_patternBinRectangle b))

theorem measurableSet_symbolGridCollision (k l q : ℕ) :
    MeasurableSet (symbolGridCollision k l q) := by
  unfold symbolGridCollision
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b => ?_))
  by_cases h : a=b
  · simp only [h,ne_eq,not_true_eq_false,Set.ofPred_false,Set.empty_inter]
    exact MeasurableSet.empty
  · simp only [h,ne_eq,not_false_eq_true,Set.ofPred_true,Set.univ_inter]
    exact MeasurableSet.iUnion (fun j =>
      ((lebesgueGridCell_measurable j).preimage (measurable_pi_apply a)).inter
        ((lebesgueGridCell_measurable j).preimage (measurable_pi_apply b)))

theorem patternBinRectangle_disjoint {k l q : ℕ} (hq : 0 < q)
    (b c : (Fin k × Fin l) → Fin q) (hbc : b ≠ c) :
    Disjoint (patternBinRectangle b) (patternBinRectangle c) := by
  obtain ⟨a,ha⟩ := Function.ne_iff.mp hbc
  apply Set.disjoint_left.mpr
  intro z hb hc
  exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hq (b a) (c a) ha)
    (Set.mem_univ_pi.mp hb a) (Set.mem_univ_pi.mp hc a)

theorem coarsePatternRealizations_subset {k l q : ℕ} (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternRealizations P q ⊆ unitOrderPatternRealizations P := by
  intro z hz
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hb,hz⟩ := Set.mem_iUnion.mp hb
  have hgood := (Finset.mem_filter.mp hb).2
  intro a c hac
  have hsep := lebesgueGrid_separation hq (hgood a c hac)
  have ha := Set.mem_univ_pi.mp hz a
  have hc := Set.mem_univ_pi.mp hz c
  change symbolGridLower (b a) < (z a : ℝ) ∧ (z a : ℝ) ≤ symbolGridUpper (b a) at ha
  change symbolGridLower (b c) < (z c : ℝ) ∧ (z c : ℝ) ≤ symbolGridUpper (b c) at hc
  exact lt_of_le_of_lt (ha.2.trans hsep) hc.1

theorem mem_coarsePatternRealizations_of_no_collision {k l q : ℕ}
    (P : LatinOrderPattern k l) (hq : 0 < q) (z : (Fin k × Fin l) → I)
    (hz : z ∈ unitOrderPatternRealizations P)
    (hcover : ∀ a, ∃ j : Fin q, z a ∈ lebesgueGridCell j)
    (hcollision : z ∉ symbolGridCollision k l q) : z ∈ coarsePatternRealizations P q := by
  choose b hb using hcover
  have hgood : ∀ a c, P a < P c → b a < b c := by
    intro a c hac
    have hne : a ≠ c := fun he => (ne_of_lt hac) (congrArg P he)
    have hbc : b a ≠ b c := by
      intro he
      exact hcollision ⟨a,c,hne,b a,hb a,by simpa only [he] using hb c⟩
    rcases lt_or_gt_of_ne hbc with hlt|hgt
    · exact hlt
    · have hsep := lebesgueGrid_separation hq hgt
      have ha := hb a
      have hc := hb c
      change symbolGridLower (b a) < (z a : ℝ) ∧ (z a : ℝ) ≤ symbolGridUpper (b a) at ha
      change symbolGridLower (b c) < (z c : ℝ) ∧ (z c : ℝ) ≤ symbolGridUpper (b c) at hc
      have hv := hz a c hac
      exact False.elim ((not_lt_of_ge (hc.2.trans hsep)) (ha.1.trans hv))
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ b,hgood⟩,Set.mem_univ_pi.mpr hb⟩⟩

end LatinonEntropy

end

-- Source: LatinonSymbolPairs.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval

theorem integral_patternConfigVertices (k l : ℕ) (F : (PatternVertex k l → I) → ℝ) :
    (∫ c, F (patternConfigVertices c) ∂latinonPatternConfigLaw k l)=
      ∫ x, F x ∂vertexSampleLaw (PatternVertex k l) :=
  (patternConfigVertices_preserving k l).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : PatternVertex k l => I)).symm.measurableEmbedding F

/-- Two distinct cells have independent uniform symbols before ordering
the sampled row/column coordinates. Shared rows and columns are allowed. -/
theorem latinonSymbolPair_integral (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) (U T : Set I)
    (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (∫ c, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U*
      (latinonSymbolKernel W (c.1 b.1,c.2 b.2)).real T ∂latinonPatternConfigLaw k l)=
      (volume : Measure I).real U*(volume : Measure I).real T := by
  let f : I × I → ℝ := fun p => (latinonSymbolKernel W p).real U
  let g : I × I → ℝ := fun p => (latinonSymbolKernel W p).real T
  have hfm : Measurable f := (measurable_latinonSymbolKernel_event W U hU).ennreal_toReal
  have hgm : Measurable g := (measurable_latinonSymbolKernel_event W T hT).ennreal_toReal
  have hfb : ∀ p, f p ∈ Set.Icc (0 : ℝ) 1 := latinonSymbolKernel_real_mem_Icc W U
  have hgb : ∀ p, g p ∈ Set.Icc (0 : ℝ) 1 := latinonSymbolKernel_real_mem_Icc W T
  have htotal : (∫ x : PatternVertex k l → I, g (x (.inl b.1),x (.inr b.2))
      ∂vertexSampleLaw (PatternVertex k l))=(volume : Measure I).real T := by
    rw [integral_vertexPair (Sum.inl b.1 : PatternVertex k l) (Sum.inr b.2) (by simp)
      g (integrable_real_latinonSymbolKernel_event W T hT)]
    exact latinonSymbolKernel_mean W T hT
  change (∫ c, f (c.1 a.1,c.2 a.2)*g (c.1 b.1,c.2 b.2) ∂latinonPatternConfigLaw k l)=_
  have he := integral_patternConfigVertices k l
    (fun x => f (x (.inl a.1),x (.inr a.2))*g (x (.inl b.1),x (.inr b.2)))
  change (∫ c, f (c.1 a.1,c.2 a.2)*g (c.1 b.1,c.2 b.2) ∂latinonPatternConfigLaw k l)=_ at he
  rw [he]
  by_cases hr : a.1=b.1
  · have hc : b.2 ≠ a.2 := fun h => hab (Prod.ext hr h.symm)
    have h := integral_vertex_leaf
      (Sum.inr a.2 : PatternVertex k l) (.inl a.1) (.inl b.1) (.inr b.2)
      (by simp) (by simp) (by simpa using hc)
      (fun p => f p.swap) g (hfm.comp measurable_swap) hgm
      (fun p => hfb p.swap) hgb ((volume : Measure I).real U)
      (latinonSymbolKernel_row_mean W U hU)
    change (∫ x : PatternVertex k l → I, f (x (.inl a.1),x (.inr a.2))*
      g (x (.inl b.1),x (.inr b.2)) ∂vertexSampleLaw (PatternVertex k l))=_ at h
    rw [h,htotal]
  · have h := integral_vertex_leaf
      (Sum.inl a.1 : PatternVertex k l) (.inr a.2) (.inl b.1) (.inr b.2)
      (by simp) (by simpa using Ne.symm hr) (by simp)
      f g hfm hgm hfb hgb ((volume : Measure I).real U)
      (latinonSymbolKernel_col_mean W U hU)
    rw [h,htotal]

theorem latinonPatternSampleLaw_symbol_event_real (W : LatinonMeasure) (k l : ℕ)
    (E : Set ((Fin k × Fin l) → I)) (hE : MeasurableSet E) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ E)=
      ∫ c, (latinonPatternSymbolKernel W k l c).real E ∂latinonPatternConfigLaw k l := by
  have h := Measure.setIntegral_compProd
    (μ := latinonPatternConfigLaw k l) (κ := latinonPatternSymbolKernel W k l)
    MeasurableSet.univ hE (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  simpa only [latinonPatternSampleLaw,setIntegral_const,smul_eq_mul,mul_one,
    Measure.restrict_univ] using h

theorem latinonPatternSymbolKernel_pair_event (W : LatinonMeasure) {k l : ℕ}
    (c : LatinonPatternConfig k l) (a b : Fin k × Fin l) (hab : a ≠ b)
    (U T : Set I) (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (latinonPatternSymbolKernel W k l c) {z | z a ∈ U ∧ z b ∈ T}=
      latinonSymbolKernel W (c.1 a.1,c.2 a.2) U*
        latinonSymbolKernel W (c.1 b.1,c.2 b.2) T := by
  let μ := fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)
  have hind := (iIndepFun_pi (μ := μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun hab
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable
  rw [(measurePreserving_eval μ a).map_eq,(measurePreserving_eval μ b).map_eq] at hmap
  have h := congrArg (fun m : Measure (I × I) => m (U ×ˢ T)) hmap
  rw [Measure.map_apply ((measurable_pi_apply a).prodMk (measurable_pi_apply b)) (hU.prod hT),
    Measure.prod_prod] at h
  exact h

theorem latinonPatternSampleLaw_pair_event_real (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) (U T : Set I)
    (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (latinonPatternSampleLaw W k l).real
      (Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T})=
        (volume : Measure I).real U*(volume : Measure I).real T := by
  have hE : MeasurableSet {z : (Fin k × Fin l) → I | z a ∈ U ∧ z b ∈ T} :=
    (hU.preimage (measurable_pi_apply a)).inter (hT.preimage (measurable_pi_apply b))
  rw [latinonPatternSampleLaw_symbol_event_real W k l
    {z : (Fin k × Fin l) → I | z a ∈ U ∧ z b ∈ T} hE]
  have hpoint (c : LatinonPatternConfig k l) :
      (latinonPatternSymbolKernel W k l c).real {z | z a ∈ U ∧ z b ∈ T}=
        (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U*
          (latinonSymbolKernel W (c.1 b.1,c.2 b.2)).real T := by
    exact (congrArg ENNReal.toReal (latinonPatternSymbolKernel_pair_event W c a b hab U T hU hT)).trans
      (ENNReal.toReal_mul)
  simp_rw [hpoint]
  exact latinonSymbolPair_integral W a b hab U T hU hT

theorem latinonPatternSampleLaw_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b))
      (latinonPatternSampleLaw W k l) unitSquareVolume := by
  have hm : Measurable (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) :=
    ((measurable_pi_apply a).comp measurable_snd).prodMk ((measurable_pi_apply b).comp measurable_snd)
  refine ⟨hm,?_⟩
  apply Measure.ext_prod
  intro U T hU hT
  have hset : (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) ⁻¹'
      (U ×ˢ T)=Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq]
  rw [Measure.map_apply hm (hU.prod hT),hset]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T})=
    unitSquareVolume.real (U ×ˢ T)
  rw [latinonPatternSampleLaw_pair_event_real W a b hab U T hU hT,measureReal_prod_prod]

theorem latinonPatternSampleLaw_single_event_real (W : LatinonMeasure) {k l : ℕ}
    (a : Fin k × Fin l) (U : Set I) (hU : MeasurableSet U) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ {z | z a ∈ U})=
      (volume : Measure I).real U := by
  have hE : MeasurableSet {z : (Fin k × Fin l) → I | z a ∈ U} := hU.preimage (measurable_pi_apply a)
  rw [latinonPatternSampleLaw_symbol_event_real W k l {z : (Fin k × Fin l) → I | z a ∈ U} hE]
  have hpoint (c : LatinonPatternConfig k l) :
      (latinonPatternSymbolKernel W k l c).real {z | z a ∈ U}=
        (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U := by
    have hm : MeasurePreserving (fun z : (Fin k × Fin l) → I => z a)
        (latinonPatternSymbolKernel W k l c) (latinonSymbolKernel W (c.1 a.1,c.2 a.2)) :=
      measurePreserving_eval (fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)) a
    exact congrArg ENNReal.toReal (hm.measure_preimage hU.nullMeasurableSet)
  simp_rw [hpoint]
  have he := integral_patternConfigVertices k l
    (fun x => (latinonSymbolKernel W (x (.inl a.1),x (.inr a.2))).real U)
  change (∫ c, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U ∂latinonPatternConfigLaw k l)=_ at he
  rw [he,integral_vertexPair (Sum.inl a.1 : PatternVertex k l) (Sum.inr a.2) (by simp)
    _ (integrable_real_latinonSymbolKernel_event W U hU)]
  exact latinonSymbolKernel_mean W U hU

theorem latinonPatternSampleLaw_single_preserving (W : LatinonMeasure) {k l : ℕ}
    (a : Fin k × Fin l) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a)
      (latinonPatternSampleLaw W k l) (volume : Measure I) := by
  have hm : Measurable (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a) :=
    (measurable_pi_apply a).comp measurable_snd
  refine ⟨hm,?_⟩
  apply Measure.ext
  intro U hU
  have hset : (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a) ⁻¹' U=
      Set.univ ×ˢ {z | z a ∈ U} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq]
  rw [Measure.map_apply hm hU,hset]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  exact latinonPatternSampleLaw_single_event_real W a U hU

end LatinonEntropy

end

-- Source: LatinonSymbolCollisions.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonPatternSampleLaw_grid_cover (W : LatinonMeasure) (k l : ℕ)
    {q : ℕ} (hq : 0 < q) :
    ∀ᵐ p ∂latinonPatternSampleLaw W k l,
      ∀ a : Fin k × Fin l, ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j := by
  simp only [ae_all_iff]
  intro a
  exact (latinonPatternSampleLaw_single_preserving W a).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hq)

theorem latinonPatternSampleLaw_pair_collision_le (W : LatinonMeasure) {k l q : ℕ}
    (hq : 0 < q) (a b : Fin k × Fin l) (hab : a ≠ b) :
    (latinonPatternSampleLaw W k l).real
      {p | ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j} ≤ 1/(q : ℝ) := by
  let E := fun j : Fin q =>
    (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) ⁻¹'
      (lebesgueGridCell j ×ˢ lebesgueGridCell j)
  have he : {p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) |
      ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j}=⋃ j, E j := by
    ext p
    simp only [E,Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_prod]
  have hmass (j : Fin q) :
      (latinonPatternSampleLaw W k l).real (E j)=(1/(q : ℝ))^2 := by
    have h := congrArg ENNReal.toReal
      ((latinonPatternSampleLaw_pair_preserving W a b hab).measure_preimage
        ((lebesgueGridCell_measurable j).prod (lebesgueGridCell_measurable j)).nullMeasurableSet)
    change (latinonPatternSampleLaw W k l).real (E j)=
      unitSquareVolume.real (lebesgueGridCell j ×ˢ lebesgueGridCell j) at h
    rw [h,measureReal_prod_prod,lebesgueGridCell_mass hq j]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : Fin q, (latinonPatternSampleLaw W k l).real (E j) :=
      measureReal_iUnion_fintype_le E
    _ = (q : ℝ)*(1/(q : ℝ))^2 := by
      simp only [hmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = 1/(q : ℝ) := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hq : (0 : ℝ) < q)]

/-- A deliberately coarse, uniform O((kl)^2/q) bound. No density bound,
finite entropy, or pointwise control of conditional marginals is used. -/
theorem latinonPatternSampleLaw_collision_le (W : LatinonMeasure) (k l : ℕ)
    {q : ℕ} (hq : 0 < q) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ symbolGridCollision k l q) ≤
      ((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  let E := fun a b : Fin k × Fin l =>
    if a=b then (∅ : Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)))
    else {p | ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j}
  have he : Set.univ ×ˢ symbolGridCollision k l q=⋃ a, ⋃ b, E a b := by
    ext p
    simp only [symbolGridCollision,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨a,b,hab,h⟩
      exact ⟨a,b,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h⟩
    · rintro ⟨a,b,h⟩
      by_cases hab : a=b
      · simp only [E,ite_eq_left hab,Set.mem_empty_iff_false] at h
      · exact ⟨a,b,hab,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h⟩
  have hcap (a b : Fin k × Fin l) :
      (latinonPatternSampleLaw W k l).real (E a b) ≤ 1/(q : ℝ) := by
    by_cases hab : a=b
    · simp only [E,ite_eq_left hab,measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg q)
    · simpa only [E,ite_eq_right hab] using latinonPatternSampleLaw_pair_collision_le W hq a b hab
  rw [he]
  calc
    _ ≤ ∑ a : Fin k × Fin l, (latinonPatternSampleLaw W k l).real (⋃ b, E a b) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin k × Fin l, ∑ b : Fin k × Fin l, (latinonPatternSampleLaw W k l).real (E a b) :=
      Finset.sum_le_sum (fun a _ => measureReal_iUnion_fintype_le (E a))
    _ ≤ ∑ _a : Fin k × Fin l, ∑ _b : Fin k × Fin l, 1/(q : ℝ) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcap a b))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul]
      ring

end LatinonEntropy

end

-- Source: LatinonCompressionPatterns.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def patternCompressionKernel {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :=
  patternEdgeKernel (latinonOrderKernel W) (latinonOrderKernel W)
    (fun a => latinonSymbolCompression W (lebesgueGridCell (b a)))

def coarsePatternDensity {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) (q : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real
    (orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q)

def compressionPatternPolynomial {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (q : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*∑ b ∈ patternBinAssignments P q,
    kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)

theorem patternCompressionKernel_measurable {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e : PatternVertex k l × PatternVertex k l) :
    Measurable (patternCompressionKernel W b e) :=
  patternEdgeKernel_measurable _ _ _ (latinonOrderKernel_measurable W)
    (latinonOrderKernel_measurable W) (fun _ => latinonSymbolCompression_measurable W _) e

theorem patternCompressionKernel_bounds {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e : PatternVertex k l × PatternVertex k l) :
    ∀ᵐ p ∂unitSquareVolume, patternCompressionKernel W b e p ∈ Set.Icc (0 : ℝ) 1 :=
  patternEdgeKernel_bounds _ _ _ (ae_of_all _ (latinonOrderKernel_bounds W))
    (ae_of_all _ (latinonOrderKernel_bounds W)) (fun _ => latinonSymbolCompression_bounds W _) e

theorem patternCompressionProduct_indicator {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (c : LatinonPatternConfig k l) :
    kernelGraphProduct (patternGraphEdges k l) (patternCompressionKernel W b) (patternConfigVertices c)=
      (orderedLatinonPatternConfigs W k l).indicator
        (fun c => ∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) c := by
  unfold patternCompressionKernel
  rw [patternGraphProduct_factor]
  change strictPairProduct (latinonOrderKernel W) c.1*strictPairProduct (latinonOrderKernel W) c.2*
    (∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2))=_
  rw [strictPairProduct_order,strictPairProduct_order]
  by_cases hr : StrictMono (W.order ∘ c.1) <;> by_cases hc : StrictMono (W.order ∘ c.2) <;>
    simp [orderedLatinonPatternConfigs,Set.indicator,hr,hc]

theorem patternSymbolRectangle_real {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (c : LatinonPatternConfig k l) :
    (latinonPatternSymbolKernel W k l c).real (patternBinRectangle b)=
      ∏ a : Fin k × Fin l, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a)) := by
  have h := congrArg ENNReal.toReal (latinonPatternSymbolKernel_rectangle W k l c
    (fun a => lebesgueGridCell (b a)))
  simpa only [Measure.real,patternBinRectangle,ENNReal.toReal_prod] using h

theorem patternSymbolProduct_ae_compression {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :
    (fun c : LatinonPatternConfig k l => ∏ a : Fin k × Fin l,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a)))=ᵐ[latinonPatternConfigLaw k l]
    (fun c => ∏ a : Fin k × Fin l,
      latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) := by
  have hall : ∀ᵐ c ∂latinonPatternConfigLaw k l, ∀ a : Fin k × Fin l,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a))=
        latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2) := by
    simp only [ae_all_iff]
    intro a
    have hm : MeasurePreserving (fun c : LatinonPatternConfig k l => (c.1 a.1,c.2 a.2))
        (latinonPatternConfigLaw k l) unitSquareVolume :=
      (vertexPair_preserving (.inl a.1 : PatternVertex k l) (.inr a.2) (by simp)).comp
        (patternConfigVertices_preserving k l)
    exact hm.quasiMeasurePreserving.ae
      (latinonSymbolKernel_ae_compression W _ (lebesgueGridCell_measurable (b a)))
  filter_upwards [hall] with c hc
  exact Finset.prod_congr rfl (fun a _ => hc a)

theorem orderedPatternBin_event_eq_graphDensity {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :
    (latinonPatternSampleLaw W k l).real
      (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b)=
        kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b) := by
  have he := Measure.setIntegral_compProd
    (μ := latinonPatternConfigLaw k l) (κ := latinonPatternSymbolKernel W k l)
    (measurableSet_orderedLatinonPatternConfigs W k l) (measurableSet_patternBinRectangle b)
    (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  have hreal : (latinonPatternSampleLaw W k l).real
      (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b)=
        ∫ c in orderedLatinonPatternConfigs W k l,
          (latinonPatternSymbolKernel W k l c).real (patternBinRectangle b) ∂latinonPatternConfigLaw k l := by
    simpa only [latinonPatternSampleLaw,setIntegral_const,smul_eq_mul,mul_one] using he
  rw [hreal]
  simp_rw [patternSymbolRectangle_real]
  calc
    _ = ∫ c in orderedLatinonPatternConfigs W k l,
        ∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)
          ∂latinonPatternConfigLaw k l :=
      integral_congr_ae (ae_restrict_of_ae (patternSymbolProduct_ae_compression W b))
    _ = ∫ c, (orderedLatinonPatternConfigs W k l).indicator
        (fun c => ∏ a : Fin k × Fin l,
          latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) c
          ∂latinonPatternConfigLaw k l :=
      (integral_indicator (measurableSet_orderedLatinonPatternConfigs W k l)).symm
    _ = ∫ c, kernelGraphProduct (patternGraphEdges k l) (patternCompressionKernel W b)
        (patternConfigVertices c) ∂latinonPatternConfigLaw k l :=
      integral_congr_ae (ae_of_all _ (fun c => (patternCompressionProduct_indicator W b c).symm))
    _ = _ := integral_patternConfigVertices k l _

/-- The approximation is an actual probability of the actual conditional
symbol sampling, represented by a finite polynomial of cut compressions. -/
theorem coarsePatternDensity_eq_polynomial {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternDensity W P q=compressionPatternPolynomial W P q := by
  unfold coarsePatternDensity compressionPatternPolynomial
  congr 1
  have he : orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q=
      ⋃ b ∈ patternBinAssignments P q, orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b := by
    ext p
    simp only [coarsePatternRealizations,Set.mem_prod,Set.mem_iUnion]
    aesop
  rw [he]
  calc
    _ = ∑ b ∈ patternBinAssignments P q, (latinonPatternSampleLaw W k l).real
        (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b) := by
      apply measureReal_biUnion_finset
      · intro b _ c _ hbc
        apply Set.disjoint_left.mpr
        intro p hb hc
        exact Set.disjoint_left.mp (patternBinRectangle_disjoint hq b c hbc) hb.2 hc.2
      · intro b _
        exact (measurableSet_orderedLatinonPatternConfigs W k l).prod (measurableSet_patternBinRectangle b)
      · intro b _
        exact measure_ne_top _ _
    _ = _ := Finset.sum_congr rfl (fun b _ => orderedPatternBin_event_eq_graphDensity W b)

end LatinonEntropy

end

-- Source: LatinonCoarseApproximation.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem coarsePatternDensity_le {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternDensity W P q ≤ latinonPatternDensity W P := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact measureReal_mono (Set.prod_mono Set.Subset.rfl (coarsePatternRealizations_subset P hq))

theorem latinonPatternDensity_coarse_error {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    |latinonPatternDensity W P-coarsePatternDensity W P q| ≤
      ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  let A := orderedLatinonPatternConfigs W k l ×ˢ unitOrderPatternRealizations P
  let B := orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q
  let C : Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
    Set.univ ×ˢ symbolGridCollision k l q
  have hmono : (latinonPatternSampleLaw W k l) (A \ B) ≤
      (latinonPatternSampleLaw W k l) C := by
    apply measure_mono_ae
    filter_upwards [latinonPatternSampleLaw_grid_cover W k l hq] with p hp
    intro hab
    refine ⟨Set.mem_univ _,?_⟩
    by_contra hn
    apply hab.2
    exact ⟨hab.1.1,mem_coarsePatternRealizations_of_no_collision P hq p.2 hab.1.2 hp hn⟩
  have hr : (latinonPatternSampleLaw W k l).real (A \ B) ≤
      (latinonPatternSampleLaw W k l).real C :=
    ENNReal.toReal_mono (measure_ne_top _ _) hmono
  have hnonneg : 0 ≤ latinonPatternDensity W P-coarsePatternDensity W P q :=
    sub_nonneg.mpr (coarsePatternDensity_le W P hq)
  rw [abs_of_nonneg hnonneg]
  change ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real A-
    ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real B ≤ _
  rw [← mul_sub]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real (A \ B) :=
      mul_le_mul_of_nonneg_left le_measureReal_sdiff (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real C :=
      mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(((k*l : ℕ) : ℝ)^2/(q : ℝ)) :=
      mul_le_mul_of_nonneg_left (latinonPatternSampleLaw_collision_le W k l hq) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem latinonPatternDensity_polynomial_error {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    |latinonPatternDensity W P-compressionPatternPolynomial W P q| ≤
      ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  rw [← coarsePatternDensity_eq_polynomial W P hq]
  exact latinonPatternDensity_coarse_error W P hq

end LatinonEntropy

end

-- Source: LatinonPatternAlignment.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinon_symbol_two_relabel_rectangle_integral (W : LatinonMeasure) (e f : LatinonRelabel)
    (U S T : Set I) (hU : MeasurableSet U) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (relabelLatinonMeasure W.measure e f).real ((S ×ˢ T) ×ˢ U)=
      ∫ p in S ×ˢ T, latinonSymbolCompression W U (e p.1,f p.2) ∂unitSquareVolume := by
  let ep : (I × I) ≃ᵐ (I × I) := e.equiv.prodCongr f.equiv
  have hm : MeasurePreserving ep unitSquareVolume unitSquareVolume := e.preserves.prod f.preserves
  have hset : ep ⁻¹' ((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T))=S ×ˢ T := by
    ext p
    change (e.symm (e p.1) ∈ S ∧ f.symm (f p.2) ∈ T) ↔ (p.1 ∈ S ∧ p.2 ∈ T)
    rw [e.symm_apply_apply,f.symm_apply_apply]
  have he := hm.setIntegral_preimage_emb ep.measurableEmbedding (latinonSymbolCompression W U)
    ((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T))
  rw [hset] at he
  rw [relabelLatinonMeasure_real_box _ e f S T U hS hT hU,
    ← latinonSymbolCompression_rectangle W U _ _ (hS.preimage e.symm.measurable) (hT.preimage f.symm.measurable)]
  exact he.symm

theorem latinon_order_relabel_rectangle_integral (W : LatinonMeasure) (e : LatinonRelabel)
    (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ p in S ×ˢ T, latinonOrderKernel W (e p.1,e p.2) ∂unitSquareVolume)=
      orderBox (W.order ∘ e) ⟨S,T,hS,hT⟩ := by
  change (∫ p in S ×ˢ T, (orderRelation (W.order ∘ e)).indicator (fun _ => (1 : ℝ)) p
    ∂unitSquareVolume)=_
  rw [setIntegral_indicator (orderRelation_measurable _ (W.order_preserving.measurable.comp e.measurable)),
    setIntegral_const,smul_eq_mul,mul_one]
  rfl

theorem orderKernel_alignment_cut (W V : LatinonMeasure) (e : LatinonRelabel) :
    KernelCutClose (latinonOrderKernel W) (fun p => latinonOrderKernel V (e p.1,e p.2))
      (orderCut W.order (V.order ∘ e)) := by
  intro S T hS hT
  have hi : Integrable (fun p : I × I => latinonOrderKernel V (e p.1,e p.2)) unitSquareVolume :=
    (e.preserves.prod e.preserves).integrable_comp_of_integrable (latinonOrderKernel_integrable V)
  rw [integral_sub (latinonOrderKernel_integrable W).integrableOn hi.integrableOn,
    ← orderBox_eq_orderKernel_integral W ⟨S,T,hS,hT⟩,
    latinon_order_relabel_rectangle_integral V e S T hS hT]
  exact orderCut_test_le W.order (V.order ∘ e) ⟨S,T,hS,hT⟩

theorem symbolGridKernel_alignment_cut (W V : LatinonMeasure) (e f : LatinonRelabel)
    {q : ℕ} (j : Fin q) :
    KernelCutClose (latinonSymbolCompression W (lebesgueGridCell j))
      (fun p => latinonSymbolCompression V (lebesgueGridCell j) (e p.1,f p.2))
      (measureCut W.measure (relabelLatinonMeasure V.measure e f)) := by
  intro S T hS hT
  have hi : Integrable (fun p : I × I => latinonSymbolCompression V (lebesgueGridCell j) (e p.1,f p.2))
      unitSquareVolume := (e.preserves.prod f.preserves).integrable_comp_of_integrable
        (latinonSymbolCompression_integrable V (lebesgueGridCell j))
  rw [integral_sub (latinonSymbolCompression_integrable W _).integrableOn hi.integrableOn,
    latinonSymbolCompression_rectangle W _ S T hS hT,
    ← latinon_symbol_two_relabel_rectangle_integral V e f _ S T (lebesgueGridCell_measurable j) hS hT]
  exact measureCut_test_le W.measure (relabelLatinonMeasure V.measure e f)
    { rows := S,cols := T,rows_measurable := hS,cols_measurable := hT,
      symbols := lebesgueGridCell j,symbols_measurable := lebesgueGridCell_measurable j,
      symbols_interval := Set.ordConnected_Ioc.preimage_mono (fun _ _ h => h) }

def patternVertexRelabel {k l : ℕ} (e f : LatinonRelabel) (v : PatternVertex k l) : I → I :=
  Sum.elim (fun _ => e) (fun _ => f) v

theorem patternVertexRelabel_preserving {k l : ℕ} (e f : LatinonRelabel) (v : PatternVertex k l) :
    MeasurePreserving (patternVertexRelabel e f v) volume volume := by
  cases v
  · exact e.preserves
  · exact f.preserves

theorem patternCompressionKernel_alignment_cut {k l q : ℕ} (W V : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e f : LatinonRelabel) (a : PatternVertex k l × PatternVertex k l) :
    KernelCutClose (patternCompressionKernel W b a)
      (fun p => patternCompressionKernel V b a
        (patternVertexRelabel e f a.1 p.1,patternVertexRelabel e f a.2 p.2))
      (latinonAlignmentCost W V e f) := by
  obtain ⟨u,v⟩ := a
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      exact fun S T hS hT => ((orderKernel_alignment_cut W V e) S T hS hT).trans
        (row_orderCut_le_alignmentCost W V e f)
    | inr j =>
      exact fun S T hS hT => ((symbolGridKernel_alignment_cut W V e f (b (i,j))) S T hS hT).trans
        (measureCut_le_alignmentCost W V e f)
  | inr i =>
    cases v with
    | inl j =>
      intro S T _ _
      simpa only [patternCompressionKernel,patternEdgeKernel,sub_self,integral_zero,abs_zero] using
        latinonAlignmentCost_nonneg W V e f
    | inr j =>
      exact fun S T hS hT => ((orderKernel_alignment_cut W V f) S T hS hT).trans
        (col_orderCut_le_alignmentCost W V e f)

theorem patternCompressionGraph_alignment {k l q : ℕ} (W V : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e f : LatinonRelabel) :
    |kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)-
      kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel V b)| ≤
        ((patternGraphEdges k l).card : ℝ)*latinonAlignmentCost W V e f := by
  let ρ := patternVertexRelabel (k := k) (l := l) e f
  have hm (a : PatternVertex k l × PatternVertex k l) :
      Measurable (fun p : I × I => patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2)) :=
    (patternCompressionKernel_measurable V b a).comp
      (((patternVertexRelabel_preserving e f a.1).measurable.comp measurable_fst).prodMk
        ((patternVertexRelabel_preserving e f a.2).measurable.comp measurable_snd))
  have hb (a : PatternVertex k l × PatternVertex k l) :
      ∀ᵐ p ∂unitSquareVolume, patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2) ∈ Set.Icc (0 : ℝ) 1 :=
    ((patternVertexRelabel_preserving e f a.1).prod (patternVertexRelabel_preserving e f a.2)).quasiMeasurePreserving.ae
      (patternCompressionKernel_bounds V b a)
  have h := kernelGraphDensity_counting_ae (patternGraphEdges k l) (patternGraphEdges_noOpposite k l)
    (patternCompressionKernel W b) (fun a p => patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2))
    (fun a _ => patternCompressionKernel_measurable W b a) (fun a _ => hm a)
    (fun a _ => patternCompressionKernel_bounds W b a) (fun a _ => hb a)
    (fun _ => latinonAlignmentCost W V e f) (fun a _ => patternCompressionKernel_alignment_cut W V b e f a)
  rw [kernelGraphDensity_nodewise_relabel (patternGraphEdges k l) (patternGraphEdges_noOpposite k l)
    (patternCompressionKernel V b) (fun a _ => patternCompressionKernel_measurable V b a)
    (fun a _ => patternCompressionKernel_bounds V b a) ρ (patternVertexRelabel_preserving e f)] at h
  simpa only [Finset.sum_const,nsmul_eq_mul] using h

def patternPolynomialConstant {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) : ℕ :=
  k.factorial*l.factorial*(patternBinAssignments P q).card*(patternGraphEdges k l).card

theorem compressionPatternPolynomial_alignment {k l : ℕ} (W V : LatinonMeasure)
    (P : LatinOrderPattern k l) (q : ℕ) (e f : LatinonRelabel) :
    |compressionPatternPolynomial W P q-compressionPatternPolynomial V P q| ≤
      (patternPolynomialConstant P q : ℝ)*latinonAlignmentCost W V e f := by
  unfold compressionPatternPolynomial
  rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),← Finset.sum_sub_distrib]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*∑ b ∈ patternBinAssignments P q,
        |kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)-
          kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel V b)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*∑ _b ∈ patternBinAssignments P q,
        ((patternGraphEdges k l).card : ℝ)*latinonAlignmentCost W V e f :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => patternCompressionGraph_alignment W V b e f))
        (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,patternPolynomialConstant,Nat.cast_mul]
      ring

end LatinonEntropy

end

-- Source: LatinonPatternContinuity.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonPatternDensity_alignment_bound {k l q : ℕ} (W V : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) (e f : LatinonRelabel) :
    |latinonPatternDensity W P-latinonPatternDensity V P| ≤
      2*(((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ))+
        (patternPolynomialConstant P q : ℝ)*latinonAlignmentCost W V e f := by
  have hW := latinonPatternDensity_polynomial_error W P hq
  have hV := latinonPatternDensity_polynomial_error V P hq
  have hpoly := compressionPatternPolynomial_alignment W V P q e f
  have h1 := abs_sub_le (latinonPatternDensity W P) (compressionPatternPolynomial W P q)
    (latinonPatternDensity V P)
  have h2 := abs_sub_le (compressionPatternPolynomial W P q) (compressionPatternPolynomial V P q)
    (latinonPatternDensity V P)
  rw [abs_sub_comm (compressionPatternPolynomial V P q)] at h2
  linarith

/-- Actual pattern densities are uniformly continuous for the full
original cut pseudometric, with both order terms and no rate hypothesis. -/
theorem uniformContinuous_latinonPatternDensity {k l : ℕ} (P : LatinOrderPattern k l) :
    UniformContinuous (fun W : LatinonMeasure => latinonPatternDensity W P) := by
  apply Metric.uniformContinuous_iff.mpr
  intro eta heta
  let B : ℝ := ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2
  obtain ⟨q,hqR⟩ := exists_nat_gt (max (1 : ℝ) (4*B/eta))
  have hqposR : (0 : ℝ) < q := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hqR)
  have hq : 0 < q := Nat.cast_pos.mp hqposR
  have hB : 2*B/(q : ℝ) < eta/2 := by
    apply (div_lt_iff₀ hqposR).mpr
    have h := (div_lt_iff₀ heta).mp ((le_max_right _ _).trans_lt hqR)
    nlinarith
  rw [mul_div_assoc] at hB
  let C : ℝ := (patternPolynomialConstant P q : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let delta := eta/(2*(C+1))
  have hden : 0 < 2*(C+1) := by positivity
  have hdelta : 0 < delta := div_pos heta hden
  refine ⟨delta,hdelta,?_⟩
  intro W V hdist
  obtain ⟨e,f,hef⟩ := exists_alignmentCost_lt W V delta hdist
  have hb := latinonPatternDensity_alignment_bound W V P hq e f
  have hc : C*latinonAlignmentCost W V e f ≤ eta/2 := by
    calc
      _ ≤ C*delta := mul_le_mul_of_nonneg_left hef.le hC
      _ ≤ (C+1)*delta := mul_le_mul_of_nonneg_right (by linarith) hdelta.le
      _ = eta/2 := by
        dsimp [delta]
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < C+1)]
  rw [Real.dist_eq]
  change |latinonPatternDensity W P-latinonPatternDensity V P| < eta
  change |latinonPatternDensity W P-latinonPatternDensity V P| ≤ 2*(B/(q : ℝ))+
    C*latinonAlignmentCost W V e f at hb
  linarith

theorem continuous_latinonPatternDensity {k l : ℕ} (P : LatinOrderPattern k l) :
    Continuous (fun W : LatinonMeasure => latinonPatternDensity W P) :=
  (uniformContinuous_latinonPatternDensity P).continuous

def latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (W : LatinonMeasure) : J → ℝ :=
  fun j => latinonPatternDensity W (P j)

theorem continuous_latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) : Continuous (latinonPatternProfile P) :=
  continuous_pi (fun j => continuous_latinonPatternDensity (P j))

end LatinonEntropy

end

-- Source: LatinonFiniteSymbolGrid.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem grid_cell_inter_real {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell j)=
      if i=j then 1/(n : ℝ) else 0 := by
  by_cases hij : i=j
  · subst j
    calc
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell i) =
          1/(n : ℝ) := by rw [Set.inter_self,lebesgueGridCell_mass hn i]
      _ = (if i=i then 1/(n : ℝ) else 0) := (ite_eq_left rfl).symm
  · have he : lebesgueGridCell i ∩ lebesgueGridCell j=∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (Set.disjoint_left.mp (lebesgueGridCell_disjoint hn i j hij) hx.1 hx.2)
      · intro hx
        exact False.elim hx
    calc
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell j) =
          (0 : ℝ) := by rw [he,measureReal_empty]
      _ = (if i=j then 1/(n : ℝ) else 0) := (ite_eq_right hij).symm

theorem finiteLatinMeasure_grid_box {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (i j s : Fin n) :
    (finiteLatinMeasure L).real ((lebesgueGridCell i ×ˢ lebesgueGridCell j) ×ˢ lebesgueGridCell s)=
      if L.val i j=s then (1/(n : ℝ))^2 else 0 := by
  have hne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  rw [finiteLatinMeasure_real_box]
  have hsum : (∑ x : Fin n, ∑ y : Fin n,
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell x)*
        volume.real (lebesgueGridCell j ∩ lebesgueGridCell y)*
          volume.real (lebesgueGridCell s ∩ lebesgueGridCell (L.val x y)))=
      volume.real (lebesgueGridCell i ∩ lebesgueGridCell i)*
        volume.real (lebesgueGridCell j ∩ lebesgueGridCell j)*
          volume.real (lebesgueGridCell s ∩ lebesgueGridCell (L.val i j)) := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · intro y _ hy
        rw [grid_cell_inter_real hn j y,ite_eq_right (Ne.symm hy)]
        simp only [mul_zero,zero_mul]
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro x _ hx
      rw [grid_cell_inter_real hn i x,ite_eq_right (Ne.symm hx)]
      simp only [zero_mul,Finset.sum_const_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  rw [hsum,Set.inter_self,Set.inter_self,lebesgueGridCell_mass hn i,lebesgueGridCell_mass hn j]
  by_cases hs : L.val i j=s
  · rw [ite_eq_left hs,hs,Set.inter_self,lebesgueGridCell_mass hn s]
    field_simp [hne]
  · rw [grid_cell_inter_real hn s (L.val i j),ite_eq_right (Ne.symm hs),ite_eq_right hs]
    simp only [mul_zero]

theorem bounded_integral_extreme_ae {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) (hfm : Measurable f)
    (hfb : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ) (hc : c=0 ∨ c=1)
    (hmean : (∫ x, f x ∂μ)=μ.real Set.univ*c) : f=ᵐ[μ] (fun _ => c) := by
  have hi := Integrable.of_mem_Icc 0 1 hfm.aemeasurable hfb
  rcases hc with rfl|rfl
  · have hn : 0 ≤ᵐ[μ] f := hfb.mono (fun _ hx => hx.1)
    apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    simpa only [mul_zero] using hmean
  · have hgi : Integrable (fun x => 1-f x) μ := (integrable_const 1).sub hi
    have hgn : 0 ≤ᵐ[μ] (fun x => 1-f x) := hfb.mono (fun _ hx => sub_nonneg.mpr hx.2)
    have hzero : (∫ x, 1-f x ∂μ)=0 := by
      rw [integral_sub (integrable_const 1) hi,integral_const]
      simp only [smul_eq_mul,mul_one] at hmean ⊢
      linarith
    have hz := (integral_eq_zero_iff_of_nonneg_ae hgn hgi).mp hzero
    filter_upwards [hz] with x hx
    change 1-f x=0 at hx
    linarith

theorem finite_symbol_grid_probability_on_box {n : ℕ} (hn : 0 < n)
    (L : LatinArray n) (i j s : Fin n) :
    ∀ᵐ p ∂unitSquareVolume, p ∈ lebesgueGridCell i ×ˢ lebesgueGridCell j →
      (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
        if L.val i j=s then (1 : ℝ) else 0 := by
  let W := latinArrayToLatinonMeasure hn L
  let S := lebesgueGridCell i ×ˢ lebesgueGridCell j
  let μ := unitSquareVolume.restrict S
  let f : I × I → ℝ := fun p => (latinonSymbolKernel W p).real (lebesgueGridCell s)
  have hS : MeasurableSet S := (lebesgueGridCell_measurable i).prod (lebesgueGridCell_measurable j)
  have hμ : μ.real Set.univ=(1/(n : ℝ))^2 := by
    change ((unitSquareVolume.restrict S) Set.univ).toReal=_
    rw [Measure.restrict_apply_univ]
    change unitSquareVolume.real (lebesgueGridCell i ×ˢ lebesgueGridCell j)=_
    rw [measureReal_prod_prod,lebesgueGridCell_mass hn i,lebesgueGridCell_mass hn j]
    ring
  have hint : (∫ p, f p ∂μ)=if L.val i j=s then (1/(n : ℝ))^2 else 0 := by
    change (∫ p in S, (latinonSymbolKernel W p).real (lebesgueGridCell s) ∂unitSquareVolume)=_
    rw [latinonSymbolKernel_real_rectangle W _ _ _ (lebesgueGridCell_measurable i)
      (lebesgueGridCell_measurable j) (lebesgueGridCell_measurable s)]
    exact finiteLatinMeasure_grid_box hn L i j s
  have he : f=ᵐ[μ] (fun _ => if L.val i j=s then (1 : ℝ) else 0) := by
    apply bounded_integral_extreme_ae μ f
      (measurable_latinonSymbolKernel_event W _ (lebesgueGridCell_measurable s)).ennreal_toReal
      (ae_of_all _ (latinonSymbolKernel_real_mem_Icc W _))
    · by_cases hs : L.val i j=s <;> simp [hs]
    · rw [hint,hμ]
      by_cases hs : L.val i j=s <;> simp [hs]
  exact (ae_restrict_iff' hS).mp he

/-- The actual conditional symbol kernel of the embedded square assigns
probability one to its matrix entry's grid bin, almost everywhere. -/
theorem finite_symbol_grid_probability {n : ℕ} (hn : 0 < n) (L : LatinArray n) :
    ∀ᵐ p ∂unitSquareVolume, ∀ s : Fin n,
      (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
        if L.val (unitGridIndex n hn p.1) (unitGridIndex n hn p.2)=s then (1 : ℝ) else 0 := by
  have hbox : ∀ᵐ p ∂unitSquareVolume, ∀ i j s : Fin n,
      p ∈ lebesgueGridCell i ×ˢ lebesgueGridCell j →
        (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
          if L.val i j=s then (1 : ℝ) else 0 := by
    simp only [ae_all_iff]
    exact fun i j s => finite_symbol_grid_probability_on_box hn L i j s
  have hx := (measurePreserving_fst (μ := (volume : Measure I)) (ν := (volume : Measure I))).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  have hy := (measurePreserving_snd (μ := (volume : Measure I)) (ν := (volume : Measure I))).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  filter_upwards [hbox,hx,hy] with p hp hpx hpy
  obtain ⟨i,hi⟩ := hpx
  obtain ⟨j,hj⟩ := hpy
  intro s
  rw [unitGridIndex_of_mem hn hi,unitGridIndex_of_mem hn hj]
  exact hp i j s ⟨hi,hj⟩

end LatinonEntropy

end

-- Source: LatinonFinitePatternIndices.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem unitGridIndex_monotone (n : ℕ) (hn : 0 < n) : Monotone (unitGridIndex n hn) := by
  intro x y hxy
  by_cases he : x=y
  · subst y
    exact le_refl _
  · by_contra hi
    have hsep := lebesgueGrid_separation hn (lt_of_not_ge hi)
    have hx := unitGridIndex_location n hn x
    have hy := unitGridIndex_location n hn y
    have hrev : (y : ℝ) ≤ (x : ℝ) := (hy.2.trans hsep).trans hx.1
    have hlt : x < y := lt_of_le_of_ne hxy he
    exact (not_lt_of_ge hrev) hlt

theorem unitGridIndex_strict_reflect (n : ℕ) (hn : 0 < n) {x y : I}
    (h : unitGridIndex n hn x < unitGridIndex n hn y) : x < y := by
  apply lt_of_not_ge
  intro hyx
  exact (not_le_of_gt h) (unitGridIndex_monotone n hn hyx)

def finiteGridIndexLaw (n : ℕ) (hn : 0 < n) : Measure (Fin n) :=
  (volume : Measure I).map (unitGridIndex n hn)

instance finiteGridIndexLaw_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (finiteGridIndexLaw n hn) := by
  refine ⟨?_⟩
  rw [finiteGridIndexLaw,Measure.map_apply (unitGridIndex_measurable n hn) MeasurableSet.univ,
    Set.preimage_univ,measure_univ]

theorem unitGridIndex_preserving (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (unitGridIndex n hn) (volume : Measure I) (finiteGridIndexLaw n hn) :=
  ⟨unitGridIndex_measurable n hn,rfl⟩

theorem finiteGridIndexLaw_real_atom (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (finiteGridIndexLaw n hn).real {i}=1/(n : ℝ) := by
  have h := congrArg ENNReal.toReal (finiteCellIndex_map_cell (volume : Measure I)
    lebesgueGridCell ⟨0,hn⟩ lebesgueGridCell_measurable (lebesgueGridCell_disjoint hn)
    (lebesgueGridCell_cover_ae hn) i)
  exact h.trans (lebesgueGridCell_mass hn i)

abbrev FinitePatternConfig (n k l : ℕ) := (Fin k → Fin n) × (Fin l → Fin n)

def finitePatternIndexLaw (n : ℕ) (hn : 0 < n) (k l : ℕ) : Measure (FinitePatternConfig n k l) :=
  (Measure.pi (fun _ : Fin k => finiteGridIndexLaw n hn)).prod
    (Measure.pi (fun _ : Fin l => finiteGridIndexLaw n hn))

instance finitePatternIndexLaw_probability (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    IsProbabilityMeasure (finitePatternIndexLaw n hn k l) := by
  unfold finitePatternIndexLaw
  infer_instance

def patternConfigGridIndices {k l : ℕ} (n : ℕ) (hn : 0 < n)
    (c : LatinonPatternConfig k l) : FinitePatternConfig n k l :=
  (fun i => unitGridIndex n hn (c.1 i),fun j => unitGridIndex n hn (c.2 j))

theorem patternConfigGridIndices_preserving (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    MeasurePreserving (patternConfigGridIndices (k := k) (l := l) n hn)
      (latinonPatternConfigLaw k l) (finitePatternIndexLaw n hn k l) :=
  (measurePreserving_pi (fun _ : Fin k => (volume : Measure I))
    (fun _ : Fin k => finiteGridIndexLaw n hn) (fun _ => unitGridIndex_preserving n hn)).prod
  (measurePreserving_pi (fun _ : Fin l => (volume : Measure I))
    (fun _ : Fin l => finiteGridIndexLaw n hn) (fun _ => unitGridIndex_preserving n hn))

theorem finitePatternIndexLaw_real_atom (n : ℕ) (hn : 0 < n) (k l : ℕ)
    (c : FinitePatternConfig n k l) :
    (finitePatternIndexLaw n hn k l).real {c}=(1/(n : ℝ))^(k+l) := by
  have hs : ({c} : Set (FinitePatternConfig n k l))={c.1} ×ˢ {c.2} := by
    exact (Set.singleton_prod_singleton).symm
  rw [hs,finitePatternIndexLaw,measureReal_prod_prod]
  simp only [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod]
  change (∏ _i : Fin k, (finiteGridIndexLaw n hn).real {c.1 _i})*
    (∏ _j : Fin l, (finiteGridIndexLaw n hn).real {c.2 _j})=_
  simp only [finiteGridIndexLaw_real_atom,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (pow_add _ _ _).symm

def finiteMatrixPatternConfigs {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (FinitePatternConfig n k l) :=
  {c | StrictMono c.1 ∧ StrictMono c.2 ∧ ∀ a b, P a < P b →
    L.val (c.1 a.1) (c.2 a.2) < L.val (c.1 b.1) (c.2 b.2)}

def finiteMatrixPatternFamily {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Finset (FinitePatternConfig n k l) := Finset.univ.filter (fun c => c ∈ finiteMatrixPatternConfigs L P)

/-- An explicit matrix count with the same k!l!/n^(k+l) coordinate
normalization as raw Latinon sampling. No embedding enters this definition. -/
def finiteMatrixPatternDensity {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*((finiteMatrixPatternFamily L P).card : ℝ)/(n : ℝ)^(k+l)

theorem finiteMatrixPatternDensity_eq_config_probability {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finiteMatrixPatternDensity L P=((k.factorial*l.factorial : ℕ) : ℝ)*
      (latinonPatternConfigLaw k l).real
        ((patternConfigGridIndices n hn) ⁻¹' finiteMatrixPatternConfigs L P) := by
  have hm := patternConfigGridIndices_preserving n hn k l
  rw [hm.measureReal_preimage (Set.toFinite (finiteMatrixPatternConfigs L P)).measurableSet.nullMeasurableSet]
  have he : finiteMatrixPatternConfigs L P=
      ⋃ c ∈ finiteMatrixPatternFamily L P, ({c} : Set (FinitePatternConfig n k l)) := by
    ext c
    simp only [Set.mem_iUnion,Set.mem_singleton_iff,finiteMatrixPatternFamily,
      Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [he]
  have hdisj : Set.PairwiseDisjoint (↑(finiteMatrixPatternFamily L P))
      (fun c : FinitePatternConfig n k l => ({c} : Set (FinitePatternConfig n k l))) := by
    intro c _ d _ hcd
    exact Set.disjoint_singleton.mpr hcd
  rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_singleton _)]
  simp only [finitePatternIndexLaw_real_atom,Finset.sum_const,nsmul_eq_mul]
  unfold finiteMatrixPatternDensity
  rw [one_div,inv_pow,div_eq_mul_inv]
  ring

end LatinonEntropy

end

-- Source: LatinonFiniteSampleSupport.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval ProbabilityTheory

theorem latinonPatternSampleLaw_config_preserving (W : LatinonMeasure) (k l : ℕ) :
    MeasurePreserving (Prod.fst : LatinonPatternConfig k l × ((Fin k × Fin l) → I) → LatinonPatternConfig k l)
      (latinonPatternSampleLaw W k l) (latinonPatternConfigLaw k l) := by
  refine ⟨measurable_fst,?_⟩
  exact Measure.fst_compProd _ _

theorem latinonPatternSampleLaw_row_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (i j : Fin k) (hij : i ≠ j) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.1.1 i,p.1.1 j))
      (latinonPatternSampleLaw W k l) unitSquareVolume :=
  ((vertexPair_preserving (Sum.inl i : PatternVertex k l) (Sum.inl j) (by simpa using hij)).comp
    (patternConfigVertices_preserving k l)).comp (latinonPatternSampleLaw_config_preserving W k l)

theorem latinonPatternSampleLaw_col_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (i j : Fin l) (hij : i ≠ j) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.1.2 i,p.1.2 j))
      (latinonPatternSampleLaw W k l) unitSquareVolume :=
  ((vertexPair_preserving (Sum.inr i : PatternVertex k l) (Sum.inr j) (by simpa using hij)).comp
    (patternConfigVertices_preserving k l)).comp (latinonPatternSampleLaw_config_preserving W k l)

/-- At the original n-grid resolution the sampled symbols of the
embedded square have exactly the matrix's labels, almost surely. -/
theorem finite_sample_symbol_indices {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) :
    ∀ᵐ p ∂latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l,
      ∀ a : Fin k × Fin l, unitGridIndex n hn (p.2 a)=
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) := by
  let W := latinArrayToLatinonMeasure hn L
  have hK : ∀ᵐ c ∂latinonPatternConfigLaw k l, ∀ a : Fin k × Fin l, ∀ s : Fin n,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell s)=
        if L.val (unitGridIndex n hn (c.1 a.1)) (unitGridIndex n hn (c.2 a.2))=s then (1 : ℝ) else 0 := by
    apply ae_all_iff.mpr
    intro a
    have hm : MeasurePreserving (fun c : LatinonPatternConfig k l => (c.1 a.1,c.2 a.2))
        (latinonPatternConfigLaw k l) unitSquareVolume :=
      (vertexPair_preserving (Sum.inl a.1 : PatternVertex k l) (Sum.inr a.2) (by simp)).comp
        (patternConfigVertices_preserving k l)
    exact hm.quasiMeasurePreserving.ae (finite_symbol_grid_probability hn L)
  apply ae_all_iff.mpr
  intro a
  let label : LatinonPatternConfig k l → Fin n := fun c =>
    L.val (unitGridIndex n hn (c.1 a.1)) (unitGridIndex n hn (c.2 a.2))
  have hl : Measurable label :=
    (measurable_of_countable (fun v : Fin n × Fin n => L.val v.1 v.2)).comp
      (((unitGridIndex_measurable n hn).comp ((measurable_pi_apply a.1).comp measurable_fst)).prodMk
        ((unitGridIndex_measurable n hn).comp ((measurable_pi_apply a.2).comp measurable_snd)))
  have hp : MeasurableSet {p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) |
      unitGridIndex n hn (p.2 a)=label p.1} :=
    measurableSet_eq_fun ((unitGridIndex_measurable n hn).comp
      ((measurable_pi_apply a).comp measurable_snd)) (hl.comp measurable_fst)
  change ∀ᵐ p ∂(latinonPatternConfigLaw k l ⊗ₘ latinonPatternSymbolKernel W k l),
    unitGridIndex n hn (p.2 a)=label p.1
  apply Measure.ae_compProd_of_ae_ae hp
  filter_upwards [hK] with c hc
  have heval : MeasurePreserving (fun z : (Fin k × Fin l) → I => z a)
      (latinonPatternSymbolKernel W k l c) (latinonSymbolKernel W (c.1 a.1,c.2 a.2)) :=
    measurePreserving_eval (fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)) a
  have hreal : (latinonPatternSymbolKernel W k l c).real
      {z | z a ∈ lebesgueGridCell (label c)}=1 := by
    have h := congrArg ENNReal.toReal (heval.measure_preimage
      (lebesgueGridCell_measurable (label c)).nullMeasurableSet)
    have hcell : (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real
        (lebesgueGridCell (label c))=1 := by
      simpa only [label,ite_true] using hc a (label c)
    exact h.trans hcell
  have hone : (latinonPatternSymbolKernel W k l c) {z | z a ∈ lebesgueGridCell (label c)}=1 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      (by
        change ((latinonPatternSymbolKernel W k l c)
          {z | z a ∈ lebesgueGridCell (label c)}).toReal=1 at hreal
        simpa only [ENNReal.toReal_one] using hreal)
  have hae : ∀ᵐ z ∂latinonPatternSymbolKernel W k l c, z a ∈ lebesgueGridCell (label c) := by
    rw [ae_iff]
    change (latinonPatternSymbolKernel W k l c) ({z | z a ∈ lebesgueGridCell (label c)}ᶜ)=0
    have hmeas : MeasurableSet {z : (Fin k × Fin l) → I |
        z a ∈ lebesgueGridCell (label c)} :=
      (lebesgueGridCell_measurable (label c)).preimage (measurable_pi_apply a)
    rw [prob_compl_eq_one_sub hmeas,hone,tsub_self]
  exact hae.mono (fun z hz => unitGridIndex_of_mem hn hz)

end LatinonEntropy

end

-- Source: LatinonFiniteIndexCollisions.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem gridIndex_pair_collision_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (f g : A → I)
    (hfg : MeasurePreserving (fun x => (f x,g x)) μ unitSquareVolume)
    (n : ℕ) (hn : 0 < n) :
    μ.real {x | unitGridIndex n hn (f x)=unitGridIndex n hn (g x)} ≤ 1/(n : ℝ) := by
  let ν := finiteGridIndexLaw n hn
  let D : Set (Fin n × Fin n) := {p | p.1=p.2}
  have hm := ((unitGridIndex_preserving n hn).prod (unitGridIndex_preserving n hn)).comp hfg
  have hmass : μ.real {x | unitGridIndex n hn (f x)=unitGridIndex n hn (g x)}=(ν.prod ν).real D :=
    hm.measureReal_preimage (Set.toFinite D).measurableSet.nullMeasurableSet
  have hD : D=⋃ i : Fin n, ({i} ×ˢ {i} : Set (Fin n × Fin n)) := by
    ext p
    simp only [D,Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_singleton_iff]
    aesop
  rw [hmass,hD]
  calc
    _ ≤ ∑ i : Fin n, (ν.prod ν).real ({i} ×ˢ {i}) := measureReal_iUnion_fintype_le _
    _ = (n : ℝ)*(1/(n : ℝ))^2 := by
      simp only [measureReal_prod_prod,ν,finiteGridIndexLaw_real_atom,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ = 1/(n : ℝ) := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

def gridIndexFamilyCollision {A J : Type*} (X : J → A → I) (n : ℕ) (hn : 0 < n) : Set A :=
  {x | ¬Function.Injective (fun j => unitGridIndex n hn (X j x))}

theorem gridIndex_family_collision_le {A J : Type*} [MeasurableSpace A] [Fintype J]
    (μ : Measure A) [IsProbabilityMeasure μ] (X : J → A → I)
    (hX : ∀ i j, i ≠ j → MeasurePreserving (fun x => (X i x,X j x)) μ unitSquareVolume)
    (n : ℕ) (hn : 0 < n) :
    μ.real (gridIndexFamilyCollision X n hn) ≤ (Fintype.card J : ℝ)^2/(n : ℝ) := by
  let E := fun a b : J => if a=b then (∅ : Set A)
    else {x | unitGridIndex n hn (X a x)=unitGridIndex n hn (X b x)}
  have he : gridIndexFamilyCollision X n hn=⋃ a, ⋃ b, E a b := by
    ext x
    simp only [gridIndexFamilyCollision,Function.Injective,not_forall,
      Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨a,b,hab,hne⟩
      exact ⟨a,b,by simpa only [E,ite_eq_right hne,Set.mem_ofPred_eq] using hab⟩
    · rintro ⟨a,b,h⟩
      by_cases hab : a=b
      · simp only [E,ite_eq_left hab,Set.mem_empty_iff_false] at h
      · exact ⟨a,b,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h,hab⟩
  have hcap (a b : J) : μ.real (E a b) ≤ 1/(n : ℝ) := by
    by_cases hab : a=b
    · simp only [E,ite_eq_left hab,measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    · simpa only [E,ite_eq_right hab] using gridIndex_pair_collision_le μ (X a) (X b) (hX a b hab) n hn
  rw [he]
  calc
    _ ≤ ∑ a : J, μ.real (⋃ b, E a b) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : J, ∑ b : J, μ.real (E a b) :=
      Finset.sum_le_sum (fun a _ => measureReal_iUnion_fintype_le (E a))
    _ ≤ ∑ _a : J, ∑ _b : J, 1/(n : ℝ) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcap a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end LatinonEntropy

end

-- Source: LatinonPatternPartition.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

theorem unitOrderPatternRealizations_iff_strictMono {k l : ℕ}
    (P : LatinOrderPattern k l) (z : (Fin k × Fin l) → I) :
    z ∈ unitOrderPatternRealizations P ↔ StrictMono (z ∘ P.symm) := by
  constructor
  · intro hz i j hij
    exact hz (P.symm i) (P.symm j) (by simpa only [Equiv.apply_symm_apply] using hij)
  · intro hz a b hab
    have h : (z (P.symm (P a)) : ℝ) < (z (P.symm (P b)) : ℝ) := hz hab
    simpa only [Equiv.symm_apply_apply] using h

theorem unitOrderPatternRealizations_injective {k l : ℕ} (P : LatinOrderPattern k l)
    (z : (Fin k × Fin l) → I) (hz : z ∈ unitOrderPatternRealizations P) : Injective z := by
  have hs := (unitOrderPatternRealizations_iff_strictMono P z).mp hz
  intro a b hab
  apply P.injective
  apply hs.injective
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hab

theorem unitOrderPatternRealizations_disjoint (k l : ℕ) :
    Pairwise (Disjoint on (fun P : LatinOrderPattern k l => unitOrderPatternRealizations P)) := by
  let P0 : LatinOrderPattern k l := Fintype.equivFinOfCardEq (by simp)
  intro P Q hPQ
  apply Set.disjoint_left.mpr
  intro z hzP hzQ
  let x : Fin (k*l) → I := z ∘ P0.symm
  let s : Equiv.Perm (Fin (k*l)) := P.symm.trans P0
  let t : Equiv.Perm (Fin (k*l)) := Q.symm.trans P0
  have hst : s ≠ t := by
    intro he
    have hinv : P.symm=Q.symm := Equiv.ext (fun i =>
      P0.injective (congrArg (fun e : Equiv.Perm (Fin (k*l)) => e i) he))
    apply hPQ
    simpa only [Equiv.symm_symm] using congrArg (fun e : Fin (k*l) ≃ (Fin k × Fin l) => e.symm) hinv
  have hs : x ∈ strictTupleChamber (k*l) s := by
    have hf : x ∘ s=z ∘ P.symm := by
      funext i
      exact congrArg z (P0.symm_apply_apply (P.symm i))
    change StrictMono (x ∘ s)
    rw [hf]
    exact (unitOrderPatternRealizations_iff_strictMono P z).mp hzP
  have ht : x ∈ strictTupleChamber (k*l) t := by
    have hf : x ∘ t=z ∘ Q.symm := by
      funext i
      exact congrArg z (P0.symm_apply_apply (Q.symm i))
    change StrictMono (x ∘ t)
    rw [hf]
    exact (unitOrderPatternRealizations_iff_strictMono Q z).mp hzQ
  exact Set.disjoint_left.mp (strictTupleChambers_disjoint (k*l) hst) hs ht

theorem unitOrderPatternRealizations_union (k l : ℕ) :
    (⋃ P : LatinOrderPattern k l, unitOrderPatternRealizations P)=
      {z : (Fin k × Fin l) → I | Injective z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hz
    exact unitOrderPatternRealizations_injective P z hP
  · intro hz
    let P0 : LatinOrderPattern k l := Fintype.equivFinOfCardEq (by simp)
    let x : Fin (k*l) → I := z ∘ P0.symm
    let s := Tuple.sort x
    let P : LatinOrderPattern k l := P0.trans s.symm
    refine Set.mem_iUnion.mpr ⟨P,?_⟩
    apply (unitOrderPatternRealizations_iff_strictMono P z).mpr
    change StrictMono (x ∘ s)
    exact (Tuple.monotone_sort x).strictMono_of_injective ((hz.comp P0.symm.injective).comp s.injective)

theorem unitSquareVolume_diagonal_zero : unitSquareVolume {p : I × I | p.1=p.2}=0 := by
  have hd : MeasurableSet {p : I × I | p.1=p.2} := (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [Measure.prod_apply hd]
  have hs (x : I) : (Prod.mk x) ⁻¹' {p : I × I | p.1=p.2}={x} := by
    ext y
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    exact eq_comm
  simp_rw [hs,measure_singleton]
  simp

theorem latinonPatternSampleLaw_ae_symbol_injective (W : LatinonMeasure) (k l : ℕ) :
    ∀ᵐ p ∂latinonPatternSampleLaw W k l, Injective p.2 := by
  simp only [Injective,ae_all_iff]
  intro a b
  by_cases hab : a=b
  · exact ae_of_all _ (fun _ _ => hab)
  · have hd : MeasurableSet {p : I × I | p.1=p.2} := (isClosed_eq continuous_fst continuous_snd).measurableSet
    have hz : (latinonPatternSampleLaw W k l) {p | p.2 a=p.2 b}=0 :=
      ((latinonPatternSampleLaw_pair_preserving W a b hab).measure_preimage hd.nullMeasurableSet).trans
        unitSquareVolume_diagonal_zero
    have hne : ∀ᵐ p ∂latinonPatternSampleLaw W k l, p.2 a ≠ p.2 b := by
      simpa only [ae_iff,Set.compl_ofPred,not_not] using hz
    filter_upwards [hne] with p hp he
    exact False.elim (hp he)

/-- Strict patterns exhaust the sampling law, even for singular Latinons. -/
theorem sum_latinonPatternDensity (W : LatinonMeasure) (k l : ℕ) :
    (∑ P : LatinOrderPattern k l, latinonPatternDensity W P)=1 := by
  let μ := latinonPatternSampleLaw W k l
  have hdisj : Pairwise (Disjoint on (fun P : LatinOrderPattern k l => latinonPatternEvent W P)) := by
    intro P Q hPQ
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (unitOrderPatternRealizations_disjoint k l hPQ) hp.2 hq.2
  have hae : (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P)=ᵐ[μ]
      (orderedLatinonPatternConfigs W k l ×ˢ Set.univ) := by
    filter_upwards [latinonPatternSampleLaw_ae_symbol_injective W k l] with p hp
    apply propext
    constructor
    · intro h
      obtain ⟨P,hP⟩ := Set.mem_iUnion.mp h
      exact ⟨hP.1,Set.mem_univ _⟩
    · intro h
      have hu : p.2 ∈ ⋃ P : LatinOrderPattern k l, unitOrderPatternRealizations P := by
        rw [unitOrderPatternRealizations_union]
        exact hp
      obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨P,h.1,hP⟩
  have hmass : μ.real (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P)=
      μ.real (orderedLatinonPatternConfigs W k l ×ˢ Set.univ) :=
    congrArg ENNReal.toReal (measure_congr hae)
  have hadd := measureReal_iUnion_fintype (μ := μ) hdisj (fun P => measurableSet_latinonPatternEvent W P)
  calc
    _ = ((k.factorial*l.factorial : ℕ) : ℝ)*∑ P : LatinOrderPattern k l, μ.real (latinonPatternEvent W P) := by
      unfold latinonPatternDensity
      rw [Finset.mul_sum]
    _ = ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (⋃ P : LatinOrderPattern k l, latinonPatternEvent W P) :=
      congrArg (fun x : ℝ => ((k.factorial*l.factorial : ℕ) : ℝ)*x) hadd.symm
    _ = 1 := by
      rw [hmass,latinonPatternSampleLaw_ordered_univ W k l,orderedLatinonPatternConfigs_normalization W k l]

end LatinonEntropy

end

-- Source: LatinonFinitePatternBridge.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev PatternSampleSpace (k l : ℕ) := LatinonPatternConfig k l × ((Fin k × Fin l) → I)

def finitePatternConfigEvent {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (LatinonPatternConfig k l) := (patternConfigGridIndices n hn) ⁻¹' finiteMatrixPatternConfigs L P

def finitePatternSampleEvent {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (PatternSampleSpace k l) := Prod.fst ⁻¹' finitePatternConfigEvent hn L P

def finitePatternBadEvent (n : ℕ) (hn : 0 < n) (k l : ℕ) : Set (PatternSampleSpace k l) :=
  (gridIndexFamilyCollision (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i) n hn ∪
    gridIndexFamilyCollision (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j) n hn) ∪
      gridIndexFamilyCollision (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a) n hn

def patternBridgeConstant (k l : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)

theorem finiteMatrixPatternDensity_eq_sample_probability {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finiteMatrixPatternDensity L P=((k.factorial*l.factorial : ℕ) : ℝ)*
      (latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l).real (finitePatternSampleEvent hn L P) := by
  rw [finiteMatrixPatternDensity_eq_config_probability hn L P]
  congr 1
  have hE : MeasurableSet (finitePatternConfigEvent hn L P) :=
    (Set.toFinite (finiteMatrixPatternConfigs L P)).measurableSet.preimage
      (patternConfigGridIndices_preserving n hn k l).measurable
  exact ((latinonPatternSampleLaw_config_preserving (latinArrayToLatinonMeasure hn L) k l).measureReal_preimage
    hE.nullMeasurableSet).symm

theorem finitePatternSampleEvent_subset_pattern_ae {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finitePatternSampleEvent hn L P ≤ᵐ[latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l]
      latinonPatternEvent (latinArrayToLatinonMeasure hn L) P := by
  filter_upwards [finite_sample_symbol_indices hn L] with p hp
  intro he
  change StrictMono (fun i => unitGridIndex n hn (p.1.1 i)) ∧
    StrictMono (fun j => unitGridIndex n hn (p.1.2 j)) ∧
      (∀ a b, P a < P b →
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) <
          L.val (unitGridIndex n hn (p.1.1 b.1)) (unitGridIndex n hn (p.1.2 b.2))) at he
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i j hij
    exact unitGridIndex_strict_reflect n hn (he.1 hij)
  · intro i j hij
    exact unitGridIndex_strict_reflect n hn (he.2.1 hij)
  · intro a b hab
    apply unitGridIndex_strict_reflect n hn
    rw [hp a,hp b]
    exact he.2.2 a b hab

theorem finitePatternSampleEvent_difference_subset_ae {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    latinonPatternEvent (latinArrayToLatinonMeasure hn L) P \ finitePatternSampleEvent hn L P
      ≤ᵐ[latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l] finitePatternBadEvent n hn k l := by
  filter_upwards [finite_sample_symbol_indices hn L] with p hp
  intro hdiff
  by_contra hnot
  have hr : Function.Injective (fun i : Fin k => unitGridIndex n hn (p.1.1 i)) := by
    by_contra h
    exact hnot (Or.inl (Or.inl h))
  have hc : Function.Injective (fun j : Fin l => unitGridIndex n hn (p.1.2 j)) := by
    by_contra h
    exact hnot (Or.inl (Or.inr h))
  have hz : Function.Injective (fun a : Fin k × Fin l => unitGridIndex n hn (p.2 a)) := by
    by_contra h
    exact hnot (Or.inr h)
  apply hdiff.2
  change StrictMono (fun i => unitGridIndex n hn (p.1.1 i)) ∧
    StrictMono (fun j => unitGridIndex n hn (p.1.2 j)) ∧
      (∀ a b, P a < P b →
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) <
          L.val (unitGridIndex n hn (p.1.1 b.1)) (unitGridIndex n hn (p.1.2 b.2)))
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    apply lt_of_le_of_ne
    · exact unitGridIndex_monotone n hn (hdiff.1.1.1 hij).le
    · exact fun he => (ne_of_lt hij) (hr he)
  · intro i j hij
    apply lt_of_le_of_ne
    · exact unitGridIndex_monotone n hn (hdiff.1.1.2 hij).le
    · exact fun he => (ne_of_lt hij) (hc he)
  · intro a b hab
    have hv : p.2 a < p.2 b := hdiff.1.2 a b hab
    have hne : a ≠ b := fun he => (ne_of_lt hab) (congrArg P he)
    have hi : unitGridIndex n hn (p.2 a) < unitGridIndex n hn (p.2 b) :=
      lt_of_le_of_ne (unitGridIndex_monotone n hn hv.le) (fun he => hne (hz he))
    simpa only [hp a,hp b] using hi

theorem finitePatternBadEvent_measure_le {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) :
    (latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l).real (finitePatternBadEvent n hn k l) ≤
      ((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)/(n : ℝ) := by
  let W := latinArrayToLatinonMeasure hn L
  let μ := latinonPatternSampleLaw W k l
  let R := gridIndexFamilyCollision (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i) n hn
  let C := gridIndexFamilyCollision (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j) n hn
  let Z := gridIndexFamilyCollision (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a) n hn
  have hr : μ.real R ≤ (k : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i)
      (fun i j hij => latinonPatternSampleLaw_row_pair_preserving W i j hij) n hn
  have hc : μ.real C ≤ (l : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j)
      (fun i j hij => latinonPatternSampleLaw_col_pair_preserving W i j hij) n hn
  have hz : μ.real Z ≤ ((k*l : ℕ) : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a)
      (fun a b hab => latinonPatternSampleLaw_pair_preserving W a b hab) n hn
  change μ.real ((R ∪ C) ∪ Z) ≤ _
  have hrc : μ.real (R ∪ C) ≤ μ.real R+μ.real C := measureReal_union_le R C
  calc
    _ ≤ μ.real (R ∪ C)+μ.real Z := measureReal_union_le _ _
    _ ≤ (μ.real R+μ.real C)+μ.real Z := add_le_add hrc (le_refl _)
    _ ≤ ((k : ℝ)^2/(n : ℝ)+(l : ℝ)^2/(n : ℝ))+((k*l : ℕ) : ℝ)^2/(n : ℝ) :=
      add_le_add (add_le_add hr hc) hz
    _ = _ := by ring

/-- Uniform transfer from the actual embedded Latinon to the explicit
finite matrix count.No surrogate statistic or density hypothesis. -/
theorem finite_matrix_pattern_embedding_error {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    |latinonPatternDensity (latinArrayToLatinonMeasure hn L) P-finiteMatrixPatternDensity L P| ≤
      patternBridgeConstant k l/(n : ℝ) := by
  let μ := latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l
  let A := latinonPatternEvent (latinArrayToLatinonMeasure hn L) P
  let E := finitePatternSampleEvent hn L P
  have hmono : μ.real E ≤ μ.real A :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (finitePatternSampleEvent_subset_pattern_ae hn L P))
  have hbad : μ.real (A \ E) ≤ μ.real (finitePatternBadEvent n hn k l) :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (finitePatternSampleEvent_difference_subset_ae hn L P))
  rw [finiteMatrixPatternDensity_eq_sample_probability hn L P]
  change |((k.factorial*l.factorial : ℕ) : ℝ)*μ.real A-
    ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real E| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (A \ E) :=
      mul_le_mul_of_nonneg_left le_measureReal_sdiff (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (finitePatternBadEvent n hn k l) :=
      mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)/(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (finitePatternBadEvent_measure_le hn L) (Nat.cast_nonneg _)
    _ = _ := by unfold patternBridgeConstant; ring

end LatinonEntropy

end

-- Source: LatinonBridge.PatternObservableCounting.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

/-- C6 instantiated with the actual vector of pattern densities.
The finite-square statistic bridge is a separate theorem. -/
theorem finite_rate_pattern_profile_entropy_count {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (z : J → ℝ) (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonPatternProfile P) z).toReal-eta)) ≤
          ((latinonEventLatinFamily (hN.trans_le hn)
            (latinonPatternProfile P ⁻¹' Metric.ball z rho)).card : ℝ) ∧
      ((latinonEventLatinFamily (hN.trans_le hn)
        (latinonPatternProfile P ⁻¹' Metric.ball z rho)).card : ℝ) ≤
          Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
            (latinonContractedRate (latinonPatternProfile P) z).toReal+eta)) :=
  finite_rate_observable_entropy_count _ (continuous_latinonPatternProfile P) z hfinite r eta hr heta

theorem closed_pattern_profile_count_upper {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (F : Set (J → ℝ)) (hF : IsClosed F) (t : ℝ)
    (ht : ∀ z ∈ F, ENNReal.ofReal t ≤ latinonContractedRate (latinonPatternProfile P) z)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ((latinonEventLatinFamily (hN.trans_le hn) (latinonPatternProfile P ⁻¹' F)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eta)) :=
  closed_observable_latin_count_upper _ (continuous_latinonPatternProfile P) F hF t ht eta heta

theorem open_pattern_profile_count_lower {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (G : Set (J → ℝ)) (hG : IsOpen G) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∃ z ∈ G, latinonContractedRate (latinonPatternProfile P) z ≤ ENNReal.ofReal t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t-eta)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (latinonPatternProfile P ⁻¹' G)).card : ℝ) :=
  open_observable_latin_count_lower _ (continuous_latinonPatternProfile P) G hG t ht0 ht eta heta

end LatinonEntropy

end

-- Source: LatinonBridge.FinitePatternEntropy.lean
noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

def finiteMatrixPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (L : LatinArray n) : J → ℝ :=
  fun j => finiteMatrixPatternDensity L (P j)

def finiteMatrixPatternBallFamily {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ) (rho : ℝ) (n : ℕ)
    [Fintype J] : Finset (LatinArray n) :=
  (allLatinSquares n).filter (fun L => finiteMatrixPatternProfile P L ∈ Metric.ball z rho)

theorem patternBridgeConstant_nonneg (k l : ℕ) : 0 ≤ patternBridgeConstant k l := by
  unfold patternBridgeConstant
  positivity

theorem finite_matrix_pattern_profile_error {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (hn : 0 < n) (L : LatinArray n) :
    dist (finiteMatrixPatternProfile P L) (latinonPatternProfile P (latinArrayToLatinonMeasure hn L)) ≤
      (∑ j, patternBridgeConstant (k j) (l j))/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : 0 ≤ ∑ j, patternBridgeConstant (k j) (l j) :=
    Finset.sum_nonneg (fun j _ => patternBridgeConstant_nonneg _ _)
  apply (dist_pi_le_iff (div_nonneg hsum hnR.le)).mpr
  intro j
  change |finiteMatrixPatternDensity L (P j)-latinonPatternDensity (latinArrayToLatinonMeasure hn L) (P j)| ≤ _
  rw [abs_sub_comm]
  exact (finite_matrix_pattern_embedding_error hn L (P j)).trans
    ((div_le_div_iff_of_pos_right hnR).mpr
      (Finset.single_le_sum (fun i _ => patternBridgeConstant_nonneg (k i) (l i)) (Finset.mem_univ j)))

theorem finite_pattern_profile_uniform_error {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n) (L : LatinArray n),
      dist (finiteMatrixPatternProfile P L)
        (latinonPatternProfile P (latinArrayToLatinonMeasure (hN.trans_le hn) L)) < eps := by
  let B := ∑ j, patternBridgeConstant (k j) (l j)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1 : ℝ) (B/eps))
  have hNpos : 0 < N := Nat.cast_pos.mp (lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN))
  refine ⟨N,hNpos,?_⟩
  intro n hn L
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hNpos.trans_le hn)
  have hlarge : B/eps < (n : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le (Nat.cast_le.mpr hn)
  have hfrac : B/(n : ℝ) < eps :=
    (div_lt_iff₀ hnR).mpr (by simpa only [mul_comm] using (div_lt_iff₀ heps).mp hlarge)
  exact (finite_matrix_pattern_profile_error P _ L).trans_lt hfrac

/-- Microcanonical counts for explicit finite MATRIX statistics, with
the contracted cost of actual Latinon pattern densities. -/
theorem finite_rate_finite_pattern_entropy_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonPatternProfile P) z).toReal-eta)) ≤
          ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ∧
      ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
          (latinonContractedRate (latinonPatternProfile P) z).toReal+eta)) := by
  let T := latinonPatternProfile P
  have hT : Continuous T := continuous_latinonPatternProfile P
  obtain ⟨rho,hrho,hrhor,U,hU,hupper⟩ := finite_rate_observable_entropy_count T hT z hfinite r eta hr heta
  obtain ⟨sigma,hsigma,hsigmar,V,hV,hlower⟩ :=
    finite_rate_observable_entropy_count T hT z hfinite (rho/4) eta (by positivity) heta
  obtain ⟨E,hE,herror⟩ := finite_pattern_profile_uniform_error P (rho/4) (by positivity)
  let N := max U (max V E)
  have hN : 0 < N := hU.trans_le (le_max_left _ _)
  refine ⟨rho/2,half_pos hrho,by linarith,N,hN,?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnV : V ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnE : E ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnp : 0 < n := hN.trans_le hn
  have herr (L : LatinArray n) :
      dist (finiteMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) < rho/4 := herror n hnE L
  have hsubL : latinonEventLatinFamily (hV.trans_le hnV) (T ⁻¹' Metric.ball z sigma) ⊆
      finiteMatrixPatternBallFamily P z (rho/2) n := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (finiteMatrixPatternProfile P L) z < rho/2
    have hb : dist (T (latinArrayToLatinonMeasure hnp L)) z < sigma := hball
    have ht := dist_triangle (finiteMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) z
    have he := herr L
    linarith
  have hsubU : finiteMatrixPatternBallFamily P z (rho/2) n ⊆
      latinonEventLatinFamily (hU.trans_le hnU) (T ⁻¹' Metric.ball z rho) := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z < rho
    have hb : dist (finiteMatrixPatternProfile P L) z < rho/2 := hball
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) < rho/4 := by
      rw [dist_comm]
      exact herr L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) z
    linarith
  exact ⟨((hlower n hnV).1).trans (Nat.cast_le.mpr (Finset.card_le_card hsubL)),
    (Nat.cast_le.mpr (Finset.card_le_card hsubU)).trans ((hupper n hnU).2)⟩

theorem empty_pattern_profile_fiber_rate_top {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (h : ¬∃ W : LatinonMeasure, latinonPatternProfile P W=z) :
    latinonContractedRate (latinonPatternProfile P) z=⊤ :=
  latinonContractedRate_outside_image _ _ h

/-- Infinite contracted cost gives arbitrary finite exponential upper
penalties.Never interprets the real value of infinity. -/
theorem infinite_rate_finite_pattern_count_upper {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hinfinite : latinonContractedRate (latinonPatternProfile P) z=⊤)
    (r t eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eta)) := by
  let T := latinonPatternProfile P
  have hT : Continuous T := continuous_latinonPatternProfile P
  have hstrict : ENNReal.ofReal t < latinonContractedRate T z := by
    rw [hinfinite]
    exact ENNReal.ofReal_lt_top
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp
    (latinonContractedRate_lowerSemicontinuous T hT z (ENNReal.ofReal t) hstrict)
  let rho := min r (delta/4)
  have hrho : 0 < rho := lt_min hr (by positivity)
  have hfloor : ∀ z' ∈ Metric.closedBall z (delta/2), ENNReal.ofReal t ≤ latinonContractedRate T z' := by
    intro z' hz'
    have hzdist : dist z' z ≤ delta/2 := hz'
    have hzin : z' ∈ Metric.ball z delta := hzdist.trans_lt (by linarith)
    exact le_of_lt (hball hzin)
  obtain ⟨U,hU,hupper⟩ := closed_observable_latin_count_upper T hT (Metric.closedBall z (delta/2))
    Metric.isClosed_closedBall t hfloor eta heta
  obtain ⟨E,hE,herror⟩ := finite_pattern_profile_uniform_error P rho hrho
  let N := max U E
  refine ⟨rho,hrho,min_le_left _ _,N,hU.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnE : E ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := hU.trans_le hnU
  have hsub : finiteMatrixPatternBallFamily P z rho n ⊆
      latinonEventLatinFamily hnp (T ⁻¹' Metric.closedBall z (delta/2)) := by
    intro L hL
    obtain ⟨hAll,hb⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z ≤ delta/2
    have hdist : dist (finiteMatrixPatternProfile P L) z < rho := hb
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) < rho := by
      rw [dist_comm]
      exact herror n hnE L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) z
    have hrhod : rho ≤ delta/4 := min_le_right _ _
    linarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hupper n hnU)

end LatinonEntropy

end

#print axioms LatinonEntropy.latinonSymbolKernel_real_mem_Icc
#print axioms LatinonEntropy.latinonSymbolKernel_row_mean
#print axioms LatinonEntropy.latinonSymbolKernel_col_mean
#print axioms LatinonEntropy.latinonSymbolKernel_mean
#print axioms LatinonEntropy.integral_resampleCoordinate
#print axioms LatinonEntropy.integral_vertexPair
#print axioms LatinonEntropy.integral_vertex_leaf
#print axioms LatinonEntropy.patternGraphEdges_noOpposite
#print axioms LatinonEntropy.patternGraphProduct_factor
#print axioms LatinonEntropy.patternEdgeKernel_measurable
#print axioms LatinonEntropy.patternEdgeKernel_bounds
#print axioms LatinonEntropy.strictPairProduct_order
#print axioms LatinonEntropy.patternConfigVertices_preserving
#print axioms LatinonEntropy.measurableSet_patternBinRectangle
#print axioms LatinonEntropy.measurableSet_coarsePatternRealizations
#print axioms LatinonEntropy.measurableSet_symbolGridCollision
#print axioms LatinonEntropy.patternBinRectangle_disjoint
#print axioms LatinonEntropy.coarsePatternRealizations_subset
#print axioms LatinonEntropy.mem_coarsePatternRealizations_of_no_collision
#print axioms LatinonEntropy.integral_patternConfigVertices
#print axioms LatinonEntropy.latinonSymbolPair_integral
#print axioms LatinonEntropy.latinonPatternSampleLaw_symbol_event_real
#print axioms LatinonEntropy.latinonPatternSymbolKernel_pair_event
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_event_real
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_single_event_real
#print axioms LatinonEntropy.latinonPatternSampleLaw_single_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_grid_cover
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_collision_le
#print axioms LatinonEntropy.latinonPatternSampleLaw_collision_le
#print axioms LatinonEntropy.patternCompressionKernel_measurable
#print axioms LatinonEntropy.patternCompressionKernel_bounds
#print axioms LatinonEntropy.patternCompressionProduct_indicator
#print axioms LatinonEntropy.patternSymbolRectangle_real
#print axioms LatinonEntropy.patternSymbolProduct_ae_compression
#print axioms LatinonEntropy.orderedPatternBin_event_eq_graphDensity
#print axioms LatinonEntropy.coarsePatternDensity_eq_polynomial
#print axioms LatinonEntropy.coarsePatternDensity_le
#print axioms LatinonEntropy.latinonPatternDensity_coarse_error
#print axioms LatinonEntropy.latinonPatternDensity_polynomial_error
#print axioms LatinonEntropy.latinon_symbol_two_relabel_rectangle_integral
#print axioms LatinonEntropy.latinon_order_relabel_rectangle_integral
#print axioms LatinonEntropy.orderKernel_alignment_cut
#print axioms LatinonEntropy.symbolGridKernel_alignment_cut
#print axioms LatinonEntropy.patternVertexRelabel_preserving
#print axioms LatinonEntropy.patternCompressionKernel_alignment_cut
#print axioms LatinonEntropy.patternCompressionGraph_alignment
#print axioms LatinonEntropy.compressionPatternPolynomial_alignment
#print axioms LatinonEntropy.latinonPatternDensity_alignment_bound
#print axioms LatinonEntropy.uniformContinuous_latinonPatternDensity
#print axioms LatinonEntropy.continuous_latinonPatternDensity
#print axioms LatinonEntropy.continuous_latinonPatternProfile
#print axioms LatinonEntropy.grid_cell_inter_real
#print axioms LatinonEntropy.finiteLatinMeasure_grid_box
#print axioms LatinonEntropy.bounded_integral_extreme_ae
#print axioms LatinonEntropy.finite_symbol_grid_probability_on_box
#print axioms LatinonEntropy.finite_symbol_grid_probability
#print axioms LatinonEntropy.unitGridIndex_monotone
#print axioms LatinonEntropy.unitGridIndex_strict_reflect
#print axioms LatinonEntropy.finiteGridIndexLaw_probability
#print axioms LatinonEntropy.unitGridIndex_preserving
#print axioms LatinonEntropy.finiteGridIndexLaw_real_atom
#print axioms LatinonEntropy.finitePatternIndexLaw_probability
#print axioms LatinonEntropy.patternConfigGridIndices_preserving
#print axioms LatinonEntropy.finitePatternIndexLaw_real_atom
#print axioms LatinonEntropy.finiteMatrixPatternDensity_eq_config_probability
#print axioms LatinonEntropy.latinonPatternSampleLaw_config_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_row_pair_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_col_pair_preserving
#print axioms LatinonEntropy.finite_sample_symbol_indices
#print axioms LatinonEntropy.gridIndex_pair_collision_le
#print axioms LatinonEntropy.gridIndex_family_collision_le
#print axioms LatinonEntropy.unitOrderPatternRealizations_iff_strictMono
#print axioms LatinonEntropy.unitOrderPatternRealizations_injective
#print axioms LatinonEntropy.unitOrderPatternRealizations_disjoint
#print axioms LatinonEntropy.unitOrderPatternRealizations_union
#print axioms LatinonEntropy.unitSquareVolume_diagonal_zero
#print axioms LatinonEntropy.latinonPatternSampleLaw_ae_symbol_injective
#print axioms LatinonEntropy.sum_latinonPatternDensity
#print axioms LatinonEntropy.finiteMatrixPatternDensity_eq_sample_probability
#print axioms LatinonEntropy.finitePatternSampleEvent_subset_pattern_ae
#print axioms LatinonEntropy.finitePatternSampleEvent_difference_subset_ae
#print axioms LatinonEntropy.finitePatternBadEvent_measure_le
#print axioms LatinonEntropy.finite_matrix_pattern_embedding_error
#print axioms LatinonEntropy.finite_rate_pattern_profile_entropy_count
#print axioms LatinonEntropy.closed_pattern_profile_count_upper
#print axioms LatinonEntropy.open_pattern_profile_count_lower
#print axioms LatinonEntropy.patternBridgeConstant_nonneg
#print axioms LatinonEntropy.finite_matrix_pattern_profile_error
#print axioms LatinonEntropy.finite_pattern_profile_uniform_error
#print axioms LatinonEntropy.finite_rate_finite_pattern_entropy_count
#print axioms LatinonEntropy.empty_pattern_profile_fiber_rate_top
#print axioms LatinonEntropy.infinite_rate_finite_pattern_count_upper
