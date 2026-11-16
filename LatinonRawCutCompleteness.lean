module

public import LatinonWeakBoxLimits
public import LatinonWeakReconstruction
public import LatinonPseudometric

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- The full comparison before taking any infimum over relabelings. -/
def latinonRawCutCost (W V : LatinonMeasure) : ℝ :=
  2*orderCut W.order V.order+measureCut W.measure V.measure

theorem latinonRawCutCost_nonneg (W V : LatinonMeasure) : 0 ≤ latinonRawCutCost W V :=
  add_nonneg (mul_nonneg (by norm_num) (orderCut_nonneg _ _)) (measureCut_nonneg _ _)

theorem latinonRawCutCost_triangle (W V Z : LatinonMeasure) :
    latinonRawCutCost W Z ≤ latinonRawCutCost W V+latinonRawCutCost V Z := by
  unfold latinonRawCutCost
  linarith only [orderCut_triangle W.order V.order Z.order,
    measureCut_triangle W.measure V.measure Z.measure]

theorem latinonCutDistance_le_rawCutCost (W V : LatinonMeasure) :
    latinonCutDistance W V ≤ latinonRawCutCost W V := by
  calc
    latinonCutDistance W V ≤ latinonAlignmentCost W V LatinonRelabel.refl LatinonRelabel.refl :=
      latinonCutDistance_le_cost W V LatinonRelabel.refl LatinonRelabel.refl
    _ = latinonRawCutCost W V := by
      change orderCut W.order V.order+orderCut W.order V.order+
        measureCut W.measure (relabelLatinonMeasure V.measure LatinonRelabel.refl
          LatinonRelabel.refl)=latinonRawCutCost W V
      rw [relabelLatinonMeasure_refl]
      simp only [latinonRawCutCost,two_mul]

/-- Actual completeness for already aligned cut-Cauchy sequences. The limit
is constructed, with all pair margins and the measure-preserving order map. -/
theorem exists_raw_latinon_cut_limit (W : ℕ → LatinonMeasure)
    (horder : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      orderCut (W m).order (W n).order < eps)
    (hmeasure : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      measureCut (W m).measure (W n).measure < eps) :
    ∃ V : LatinonMeasure, Tendsto (fun n => latinonRawCutCost (W n) V) atTop (𝓝 0) := by
  obtain ⟨V,phi,hphi,hw,ho⟩ := exists_joint_weak_order_limit W horder
  have hmc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      measureCut (W (phi m)).measure (W (phi n)).measure < eps := by
    intro eps heps
    obtain ⟨N,hN⟩ := hmeasure eps heps
    exact ⟨N,fun m hm n hn => hN (phi m) (hm.trans (hphi.id_le m))
      (phi n) (hn.trans (hphi.id_le n))⟩
  have hm := measureCut_limit_of_weak_and_Cauchy (fun n => W (phi n)) V hw hmc
  have hsub : Tendsto (fun n => latinonRawCutCost (W (phi n)) V) atTop (𝓝 0) := by
    simpa only [latinonRawCutCost,mul_zero,add_zero] using (ho.const_mul 2).add hm
  have hrawC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      latinonRawCutCost (W m) (W n) < eps := by
    intro eps heps
    obtain ⟨N,hN⟩ := horder (eps/4) (by positivity)
    obtain ⟨M,hM⟩ := hmeasure (eps/2) (by positivity)
    refine ⟨max N M,?_⟩
    intro m hm n hn
    have h1 := hN m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
    have h2 := hM m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    unfold latinonRawCutCost
    linarith only [h1,h2]
  refine ⟨V,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (latinonRawCutCost_nonneg _ _))
  · intro eps heps
    obtain ⟨N,hN⟩ := hrawC (eps/2) (by positivity)
    obtain ⟨K,hK⟩ := eventually_atTop.mp (hsub.eventually_lt_const (half_pos heps))
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 := hN n hn (phi (max K N)) ((le_max_right K N).trans (hphi.id_le _))
    have h2 := hK (max K N) (le_max_left _ _)
    have htri := latinonRawCutCost_triangle (W n) (W (phi (max K N))) V
    linarith only [h1,h2,htri]

theorem exists_latinon_limit_of_raw_Cauchy (W : ℕ → LatinonMeasure)
    (horder : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      orderCut (W m).order (W n).order < eps)
    (hmeasure : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      measureCut (W m).measure (W n).measure < eps) :
    ∃ V : LatinonMeasure, Tendsto W atTop (𝓝 V) := by
  obtain ⟨V,hV⟩ := exists_raw_latinon_cut_limit W horder hmeasure
  refine ⟨V,tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun n => dist_nonneg)
    (fun n => latinonCutDistance_le_rawCutCost (W n) V) hV

end LatinonEntropy

#print axioms LatinonEntropy.latinonRawCutCost_nonneg
#print axioms LatinonEntropy.latinonRawCutCost_triangle
#print axioms LatinonEntropy.latinonCutDistance_le_rawCutCost
#print axioms LatinonEntropy.exists_raw_latinon_cut_limit
#print axioms LatinonEntropy.exists_latinon_limit_of_raw_Cauchy
