module

public import LatinonSynchronousAction
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- An auxiliary stronger distance,used only to construct common alignments.
The original full Latinon distance and its topology are unchanged. -/
def synchronousCutDistance (W V : LatinonMeasure) : ℝ :=
  sInf (Set.range (fun e : LatinonRelabel => latinonAlignmentCost W V e e))

theorem synchronousCost_range_nonempty (W V : LatinonMeasure) :
    (Set.range (fun e : LatinonRelabel => latinonAlignmentCost W V e e)).Nonempty :=
  ⟨_,⟨LatinonRelabel.refl,rfl⟩⟩

theorem synchronousCost_range_bddBelow (W V : LatinonMeasure) :
    BddBelow (Set.range (fun e : LatinonRelabel => latinonAlignmentCost W V e e)) :=
  ⟨0,by rintro _ ⟨e,rfl⟩; exact latinonAlignmentCost_nonneg W V e e⟩

theorem synchronousCutDistance_nonneg (W V : LatinonMeasure) : 0 ≤ synchronousCutDistance W V :=
  le_csInf (synchronousCost_range_nonempty W V)
    (by rintro _ ⟨e,rfl⟩; exact latinonAlignmentCost_nonneg W V e e)

theorem synchronousCutDistance_le_cost (W V : LatinonMeasure) (e : LatinonRelabel) :
    synchronousCutDistance W V ≤ latinonAlignmentCost W V e e :=
  csInf_le (synchronousCost_range_bddBelow W V) ⟨e,rfl⟩

theorem synchronousCutDistance_le_rawCost (W V : LatinonMeasure) :
    synchronousCutDistance W V ≤ latinonRawCutCost W V := by
  have h := synchronousCutDistance_le_cost W V LatinonRelabel.refl
  rw [← rawCutCost_synchronous_eq_alignmentCost,synchronousRelabel_refl] at h
  exact h

theorem synchronousCutDistance_self (W : LatinonMeasure) : synchronousCutDistance W W=0 := by
  have h := synchronousCutDistance_le_rawCost W W
  simp only [latinonRawCutCost,orderCut_self,measureCut_self,mul_zero,add_zero] at h
  exact le_antisymm h (synchronousCutDistance_nonneg W W)

theorem synchronousCutDistance_le_reverse (W V : LatinonMeasure) :
    synchronousCutDistance W V ≤ synchronousCutDistance V W := by
  apply le_csInf (synchronousCost_range_nonempty V W)
  rintro _ ⟨e,rfl⟩
  exact (synchronousCutDistance_le_cost W V e.symm).trans_eq
    (latinonAlignmentCost_inverse V W e e).symm

theorem synchronousCutDistance_symm (W V : LatinonMeasure) :
    synchronousCutDistance W V=synchronousCutDistance V W :=
  le_antisymm (synchronousCutDistance_le_reverse W V) (synchronousCutDistance_le_reverse V W)

theorem exists_synchronousCost_lt (W V : LatinonMeasure) (delta : ℝ)
    (h : synchronousCutDistance W V < delta) :
    ∃ e : LatinonRelabel, latinonAlignmentCost W V e e < delta := by
  by_contra hn
  have hl : delta ≤ synchronousCutDistance W V := by
    apply le_csInf (synchronousCost_range_nonempty W V)
    rintro _ ⟨e,rfl⟩
    exact le_of_not_gt (fun he => hn ⟨e,he⟩)
  exact (not_lt_of_ge hl) h

theorem synchronousCutDistance_triangle (W V U : LatinonMeasure) :
    synchronousCutDistance W U ≤ synchronousCutDistance W V+synchronousCutDistance V U := by
  by_contra hn
  have hgt := lt_of_not_ge hn
  let eps := (synchronousCutDistance W U-(synchronousCutDistance W V+synchronousCutDistance V U))/3
  have heps : 0 < eps := div_pos (sub_pos.mpr hgt) (by norm_num)
  obtain ⟨e,h1⟩ := exists_synchronousCost_lt W V (synchronousCutDistance W V+eps) (by linarith only [heps])
  obtain ⟨g,h2⟩ := exists_synchronousCost_lt V U (synchronousCutDistance V U+eps) (by linarith only [heps])
  have ht := latinonAlignmentCost_triangle W V U e e g g
  have hl := synchronousCutDistance_le_cost W U (e.trans g)
  dsimp only [eps] at h1 h2
  linarith only [h1,h2,ht,hl,hgt]

theorem latinonCutDistance_le_synchronous (W V : LatinonMeasure) :
    latinonCutDistance W V ≤ synchronousCutDistance W V := by
  apply le_csInf (synchronousCost_range_nonempty W V)
  rintro _ ⟨e,rfl⟩
  exact latinonCutDistance_le_cost W V e e

/-- A separate type prevents replacing the original full-distance instance. -/
structure SynchronousLatinon where
  value : LatinonMeasure

instance : PseudoMetricSpace SynchronousLatinon where
  dist W V := synchronousCutDistance W.value V.value
  dist_self W := synchronousCutDistance_self W.value
  dist_comm W V := synchronousCutDistance_symm W.value V.value
  dist_triangle W V U := synchronousCutDistance_triangle W.value V.value U.value

theorem synchronousLatinon_forget_lipschitz :
    LipschitzWith 1 (SynchronousLatinon.value : SynchronousLatinon → LatinonMeasure) := by
  apply LipschitzWith.of_dist_le_mul
  intro W V
  change latinonCutDistance W.value V.value ≤ (1 : ℝ)*synchronousCutDistance W.value V.value
  rw [one_mul]
  exact latinonCutDistance_le_synchronous W.value V.value

theorem synchronousLatinon_forget_continuous :
    Continuous (SynchronousLatinon.value : SynchronousLatinon → LatinonMeasure) :=
  synchronousLatinon_forget_lipschitz.continuous

theorem synchronousCutDistance_relabel_zero (W : LatinonMeasure) (e : LatinonRelabel) :
    synchronousCutDistance (synchronousRelabel W e) W=0 := by
  have hc : latinonAlignmentCost (synchronousRelabel W e) W e e=0 := by
    rw [← rawCutCost_synchronous_eq_alignmentCost]
    simp only [latinonRawCutCost,orderCut_self,measureCut_self,mul_zero,add_zero]
  exact le_antisymm ((synchronousCutDistance_le_cost _ _ e).trans_eq hc)
    (synchronousCutDistance_nonneg _ _)

end LatinonEntropy

#print axioms LatinonEntropy.synchronousCost_range_nonempty
#print axioms LatinonEntropy.synchronousCost_range_bddBelow
#print axioms LatinonEntropy.synchronousCutDistance_nonneg
#print axioms LatinonEntropy.synchronousCutDistance_le_cost
#print axioms LatinonEntropy.synchronousCutDistance_le_rawCost
#print axioms LatinonEntropy.synchronousCutDistance_self
#print axioms LatinonEntropy.synchronousCutDistance_symm
#print axioms LatinonEntropy.exists_synchronousCost_lt
#print axioms LatinonEntropy.synchronousCutDistance_triangle
#print axioms LatinonEntropy.latinonCutDistance_le_synchronous
#print axioms LatinonEntropy.synchronousLatinon_forget_lipschitz
#print axioms LatinonEntropy.synchronousLatinon_forget_continuous
#print axioms LatinonEntropy.synchronousCutDistance_relabel_zero
