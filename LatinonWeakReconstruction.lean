module

public import LatinonWeakMarginalCompactness
public import OrderMapCompleteness

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- Reconstruct an actual Latinon from a weak limiting law and an actual MP
order map. The pair margins are recovered from the three pushforward laws. -/
def latinonOfUniformPairs (nu : ProbabilityMeasure LatinonPoint)
    (hnu : nu ∈ uniformPairProbabilitySet) (g : I → I)
    (hg : MeasurePreserving g volume volume) : LatinonMeasure where
  measure := nu
  order := g
  order_preserving := hg
  xy_uniform := by
    intro S T hS hT
    have he : (nu : Measure LatinonPoint).map Prod.fst=unitSquareVolume :=
      congrArg Subtype.val hnu.1
    have h := congrArg (fun mu : Measure (I × I) => mu (S ×ˢ T)) he
    rw [Measure.map_apply measurable_fst (hS.prod hT),Measure.prod_prod] at h
    convert h using 2
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  xz_uniform := by
    intro S U hS hU
    have he : (nu : Measure LatinonPoint).map latinonXZProjection=unitSquareVolume :=
      congrArg Subtype.val hnu.2.1
    have hm : Measurable latinonXZProjection :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h := congrArg (fun mu : Measure (I × I) => mu (S ×ˢ U)) he
    rw [Measure.map_apply hm (hS.prod hU),Measure.prod_prod] at h
    convert h using 2
    ext p
    simp only [latinonXZProjection,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  yz_uniform := by
    intro T U hT hU
    have he : (nu : Measure LatinonPoint).map latinonYZProjection=unitSquareVolume :=
      congrArg Subtype.val hnu.2.2
    have hm : Measurable latinonYZProjection :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have h := congrArg (fun mu : Measure (I × I) => mu (T ×ˢ U)) he
    rw [Measure.map_apply hm (hT.prod hU),Measure.prod_prod] at h
    convert h using 2
    ext p
    simp only [latinonYZProjection,Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]

theorem latinonProbability_ofUniformPairs (nu : ProbabilityMeasure LatinonPoint)
    (hnu : nu ∈ uniformPairProbabilitySet) (g : I → I)
    (hg : MeasurePreserving g volume volume) :
    latinonProbability (latinonOfUniformPairs nu hnu g hg)=nu := by
  apply Subtype.ext
  rfl

/-- Joint weak-distribution and order-cut convergence to an actual Latinon.
Distribution cut convergence is a separate obligation. -/
theorem exists_joint_weak_order_limit (W : ℕ → LatinonMeasure)
    (horder : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      orderCut (W m).order (W n).order < eps) :
    ∃ V : LatinonMeasure, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => latinonProbability (W (phi n))) atTop (𝓝 (latinonProbability V)) ∧
      Tendsto (fun n => orderCut (W (phi n)).order V.order) atTop (𝓝 0) := by
  obtain ⟨g,hg,hglim⟩ := exists_MP_orderCut_limit (fun n => (W n).order)
    (fun n => (W n).order_preserving) horder
  obtain ⟨nu,hnu,phi,hphi,hlim⟩ := exists_weak_subsequence_uniform_pair_margins W
  refine ⟨latinonOfUniformPairs nu hnu g hg,phi,hphi,?_,?_⟩
  · simpa only [latinonProbability_ofUniformPairs] using hlim
  · exact hglim.comp hphi.tendsto_atTop

end LatinonEntropy

#print axioms LatinonEntropy.latinonOfUniformPairs
#print axioms LatinonEntropy.latinonProbability_ofUniformPairs
#print axioms LatinonEntropy.exists_joint_weak_order_limit
