module

public import GridIntervalPermutation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

def gridLowerPoint {n : ℕ} (hn : 0 < n) (i : Fin n) : I :=
  ⟨symbolGridLower i,gridLower_nonneg i,
    (sub_nonneg.mp (symbolGrid_width_nonneg i)).trans (gridUpper_le_one hn i)⟩

theorem gridLowerPoint_dist {n : ℕ} (hn : 0 < n) (u : I) :
    dist u (gridLowerPoint hn (unitGridIndex n hn u)) ≤ 1/(n : ℝ) := by
  rw [Subtype.dist_eq,Real.dist_eq]
  exact unitGridIndex_error n hn u

/-- Every integrable real function has arbitrarily accurate uniform-grid
step approximations for ALL sufficiently large grid sizes. -/
theorem exists_all_sizes_grid_step_L1 (f : I → ℝ) (hf : Integrable f volume)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∃ a : Fin n → ℝ, Integrable (fun u => a (unitGridIndex n (hN.trans_le hn) u)) volume ∧
        (∫ u, |f u-a (unitGridIndex n (hN.trans_le hn) u)|) ≤ eps := by
  obtain ⟨g,hfg,hg⟩ := hf.exists_boundedContinuous_integral_sub_le (half_pos heps)
  simp only [Real.norm_eq_abs] at hfg
  have huc := CompactSpace.uniformContinuous_of_continuous g.continuous
  obtain ⟨delta,hd,hclose⟩ := Metric.uniformContinuous_iff.mp huc (eps/2) (half_pos heps)
  obtain ⟨K,hK⟩ := exists_nat_gt (1/delta)
  refine ⟨K+1,by omega,?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < K+1) hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hbig : 1/delta < (n : ℝ) := hK.trans (by exact_mod_cast (show K < n by omega))
  have hinv : 1/(n : ℝ) < delta := by
    apply (div_lt_iff₀ hnR).mpr
    have hprod := (div_lt_iff₀ hd).mp hbig
    nlinarith only [hprod]
  let a : Fin n → ℝ := fun i => g (gridLowerPoint hnpos i)
  have haM : Measurable (fun u => a (unitGridIndex n hnpos u)) :=
    (measurable_of_countable a).comp (unitGridIndex_measurable n hnpos)
  have ha : Integrable (fun u => a (unitGridIndex n hnpos u)) volume :=
    Integrable.of_bound haM.aestronglyMeasurable ‖g‖
      (ae_of_all _ fun u => g.norm_coe_le_norm _)
  refine ⟨a,ha,?_⟩
  have hp : ∀ u : I, |g u-a (unitGridIndex n hnpos u)| ≤ eps/2 := by
    intro u
    have hh := hclose ((gridLowerPoint_dist hnpos u).trans_lt hinv)
    exact (show |g u-a (unitGridIndex n hnpos u)| < eps/2 from hh).le
  have hfgInt : Integrable (fun u => |f u-g u|) volume := (hf.sub hg).abs
  have hfaInt : Integrable (fun u => |f u-a (unitGridIndex n hnpos u)|) volume := (hf.sub ha).abs
  calc
    (∫ u, |f u-a (unitGridIndex n hnpos u)|)
        ≤ ∫ u, |f u-g u|+eps/2 := by
          apply integral_mono hfaInt (hfgInt.add (integrable_const _))
          intro u
          exact (abs_sub_le (f u) (g u) (a (unitGridIndex n hnpos u))).trans
            (add_le_add le_rfl (hp u))
    _ = (∫ u, |f u-g u|)+eps/2 := by
      rw [integral_add hfgInt (integrable_const _),integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
    _ ≤ eps := by linarith only [hfg]

end LatinonEntropy

#print axioms LatinonEntropy.gridLowerPoint_dist
#print axioms LatinonEntropy.exists_all_sizes_grid_step_L1
