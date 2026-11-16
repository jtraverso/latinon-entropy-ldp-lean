module

/- Local bridge for the Latinon compactness proof; not an upstream Graphon file. -/
public import Graphon.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval NNReal ENNReal

def binaryTagMeasure : Measure Bool :=
  (1/2 : ℝ≥0) • (Measure.dirac false+Measure.dirac true)

instance : IsProbabilityMeasure binaryTagMeasure := by
  constructor
  have h : (1/2 : ℝ≥0)*(1+1)=1 := by norm_num
  have he : (((1/2 : ℝ≥0) : ℝ≥0∞)*(1+1))=1 := by exact_mod_cast h
  simpa only [binaryTagMeasure,Measure.coe_nnreal_smul_apply,Measure.add_apply,measure_univ] using he

abbrev BipartiteSpace := Bool × I
abbrev bipartiteVolume : Measure BipartiteSpace := binaryTagMeasure.prod volume

/-- A directed kernel occupies the two off-diagonal blocks of a symmetric one. -/
def bipartiteValue (g : I × I → ℝ) (p : BipartiteSpace × BipartiteSpace) : ℝ :=
  if p.1.1=false ∧ p.2.1=true then g (p.1.2,p.2.2)
  else if p.1.1=true ∧ p.2.1=false then g (p.2.2,p.1.2) else 0

theorem bipartiteValue_measurable (g : I × I → ℝ) (hg : Measurable g) :
    Measurable (bipartiteValue g) := by
  unfold bipartiteValue
  have h01 : MeasurableSet {p : BipartiteSpace × BipartiteSpace | p.1.1=false ∧ p.2.1=true} :=
    ((measurableSet_singleton false).preimage (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_singleton true).preimage (measurable_fst.comp measurable_snd))
  have h10 : MeasurableSet {p : BipartiteSpace × BipartiteSpace | p.1.1=true ∧ p.2.1=false} :=
    ((measurableSet_singleton true).preimage (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_singleton false).preimage (measurable_fst.comp measurable_snd))
  have hxy : Measurable (fun p : BipartiteSpace × BipartiteSpace => (p.1.2,p.2.2)) :=
    (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hyx : Measurable (fun p : BipartiteSpace × BipartiteSpace => (p.2.2,p.1.2)) :=
    (measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)
  exact Measurable.ite h01 (hg.comp hxy) (Measurable.ite h10 (hg.comp hyx) measurable_const)

theorem bipartiteValue_symm (g : I × I → ℝ) (p : BipartiteSpace × BipartiteSpace) :
    bipartiteValue g p.swap = bipartiteValue g p := by
  rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩
  cases i <;> cases j <;> simp [bipartiteValue]

theorem bipartiteValue_bounds (g : I × I → ℝ)
    (hg : ∀ᵐ p ∂((volume : Measure I).prod volume), g p ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂(bipartiteVolume.prod bipartiteVolume), bipartiteValue g p ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : MeasurePreserving (Prod.snd : BipartiteSpace → I) bipartiteVolume volume :=
    measurePreserving_snd
  have hxy := hs.prod hs
  filter_upwards [hxy.quasiMeasurePreserving.ae hg,
    hxy.quasiMeasurePreserving.ae (ae_prod_swap hg)] with p hp hq
  unfold bipartiteValue
  split_ifs
  · exact hp
  · exact hq
  · constructor <;> norm_num

def bipartiteGraphon (g : I × I → ℝ) (hmeas : Measurable g)
    (hb : ∀ᵐ p ∂((volume : Measure I).prod volume), g p ∈ Set.Icc (0 : ℝ) 1) :
    Graphon BipartiteSpace bipartiteVolume where
  toSymmKernel := {
    toAEEqFun := AEEqFun.mk (bipartiteValue g) (bipartiteValue_measurable g hmeas).aestronglyMeasurable
    symm' := by
      have he := AEEqFun.coeFn_mk (μ := bipartiteVolume.prod bipartiteVolume)
        (bipartiteValue g) (bipartiteValue_measurable g hmeas).aestronglyMeasurable
      have hes := ae_prod_swap he
      filter_upwards [he,hes] with p hp hps
      rw [hp,hps,bipartiteValue_symm] }
  ae_mem_Icc := by
    have he := AEEqFun.coeFn_mk (μ := bipartiteVolume.prod bipartiteVolume)
      (bipartiteValue g) (bipartiteValue_measurable g hmeas).aestronglyMeasurable
    filter_upwards [he,bipartiteValue_bounds g hb] with p hp hbound
    rwa [hp]

theorem bipartiteValue_forward (g : I × I → ℝ) (x y : I) :
    bipartiteValue g ((false,x),(true,y)) = g (x,y) := rfl

end LatinonEntropy

#print axioms LatinonEntropy.bipartiteValue_measurable
#print axioms LatinonEntropy.bipartiteValue_symm
#print axioms LatinonEntropy.bipartiteValue_bounds
#print axioms LatinonEntropy.bipartiteGraphon
#print axioms LatinonEntropy.bipartiteValue_forward
