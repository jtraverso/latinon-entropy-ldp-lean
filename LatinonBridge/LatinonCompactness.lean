module

public import LatinonBridge.CommonKernelNets
public import LatinonKernelFamily
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- Finite common-kernel discretizations give actual total boundedness
of the auxiliary synchronous Latinon space. -/
theorem synchronousLatinon_totallyBounded : TotallyBounded (Set.univ : Set SynchronousLatinon) := by
  apply Metric.totallyBounded_of_finite_discretization
  intro eps heps
  let n := Nat.ceil (16/eps)+1
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnl : 16/eps ≤ (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith only [Nat.le_ceil (16/eps)]
  have hnb : 4/(n : ℝ) ≤ eps/4 := by
    apply (div_le_iff₀ hnR).mpr
    have hp := (div_le_iff₀ heps).mp hnl
    nlinarith only [hp]
  let delta := eps/(4*((n : ℝ)+2))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hbudget : ((n : ℝ)+2)*(2*delta)+4/(n : ℝ) < eps := by
    have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
    have hhalf : ((n : ℝ)+2)*(2*delta)=eps/2 := by
      dsimp [delta]
      field_simp [hn2]; ring
    rw [hhalf]
    linarith only [hnb,heps]
  obtain ⟨net,hnet,hcover⟩ := exists_common_kernel_family_net (n+1) delta hd
  choose e v hv hclose using (fun W : SynchronousLatinon => hcover (latinonKernelFamily W.value n)
    (latinonKernelFamily_measurable W.value n) (latinonKernelFamily_bounds W.value n))
  let F : {W : SynchronousLatinon // W ∈ (Set.univ : Set SynchronousLatinon)} →
      {v // v ∈ net} := fun W => ⟨v W.1,hv W.1⟩
  refine ⟨{v // v ∈ net},inferInstance,F,?_⟩
  intro x y hxy
  have heq : v x.1=v y.1 := congrArg Subtype.val hxy
  have hy : ∀ j, KernelCutClose
      (fun p => latinonKernelFamily y.1.value n j (e y.1 p.1,e y.1 p.2)) (v x.1 j) delta := by
    rw [heq]
    exact hclose y.1
  have hraw := rawCutCost_le_of_common_family_approximation x.1.value y.1.value hn (e x.1) (e y.1)
    (v x.1) (hnet _ (hv x.1)) delta hd.le (hclose x.1) hy
  have hdist := (synchronousCutDistance_le_aligned_rawCost x.1.value y.1.value (e x.1) (e y.1)).trans hraw
  change synchronousCutDistance x.1.value y.1.value < eps
  exact hdist.trans_lt hbudget

instance : CompactSpace SynchronousLatinon :=
  ⟨isCompact_iff_totallyBounded_isComplete.mpr ⟨synchronousLatinon_totallyBounded,isComplete_univ⟩⟩

/-- Compactness in the ORIGINAL full Latinon distance,including both order
terms,as a continuous image of the complete totally bounded auxiliary space. -/
theorem latinon_full_cut_compact : IsCompact (Set.univ : Set LatinonMeasure) := by
  have he : SynchronousLatinon.value '' (Set.univ : Set SynchronousLatinon)=(Set.univ : Set LatinonMeasure) :=
    Set.eq_univ_of_forall (fun W => ⟨⟨W⟩,Set.mem_univ _,rfl⟩)
  rw [← he]
  exact isCompact_univ.image synchronousLatinon_forget_continuous

instance : CompactSpace LatinonMeasure := ⟨latinon_full_cut_compact⟩

theorem latinon_closed_set_compact (F : Set LatinonMeasure) (hF : IsClosed F) : IsCompact F := hF.isCompact

end LatinonEntropy

#print axioms LatinonEntropy.synchronousLatinon_totallyBounded
#print axioms LatinonEntropy.latinon_full_cut_compact
#print axioms LatinonEntropy.latinon_closed_set_compact
