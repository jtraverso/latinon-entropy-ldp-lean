module

public import UnitGridL1Approximation
public import DyadicCubeFiltration

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev unitCubeVolume : Measure ((I × I) × I) := ((volume : Measure I).prod volume).prod volume

def gridCubeLowerPoint {n : ℕ} (hn : 0 < n) (b : (Fin n × Fin n) × Fin n) : (I × I) × I :=
  ((gridLowerPoint hn b.1.1,gridLowerPoint hn b.1.2),gridLowerPoint hn b.2)

theorem gridCubeLowerPoint_dist {n : ℕ} (hn : 0 < n) (p : (I × I) × I) :
    dist p (gridCubeLowerPoint hn (coordinateGridIndex n hn p)) ≤ 1/(n : ℝ) := by
  change max (max (dist p.1.1 (gridLowerPoint hn (unitGridIndex n hn p.1.1)))
    (dist p.1.2 (gridLowerPoint hn (unitGridIndex n hn p.1.2))))
    (dist p.2 (gridLowerPoint hn (unitGridIndex n hn p.2))) ≤ _
  exact max_le (max_le (gridLowerPoint_dist hn p.1.1) (gridLowerPoint_dist hn p.1.2))
    (gridLowerPoint_dist hn p.2)

/-- L1 density by cube grid steps,for every sufficiently large size.
This is an approximation theorem for actual integrable functions; no
convergence of the Latinon coarsening is assumed. -/
theorem exists_all_sizes_cube_grid_step_L1 (f : (I × I) × I → ℝ)
    (hf : Integrable f unitCubeVolume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∃ a : (Fin n × Fin n) × Fin n → ℝ,
        Integrable (fun p => a (coordinateGridIndex n (hN.trans_le hn) p)) unitCubeVolume ∧
          (∫ p, |f p-a (coordinateGridIndex n (hN.trans_le hn) p)| ∂unitCubeVolume) ≤ eps := by
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
  let a : (Fin n × Fin n) × Fin n → ℝ := fun b => g (gridCubeLowerPoint hnpos b)
  have haM : Measurable (fun p => a (coordinateGridIndex n hnpos p)) :=
    (measurable_of_countable a).comp (coordinateGridIndex_measurable n hnpos)
  have ha : Integrable (fun p => a (coordinateGridIndex n hnpos p)) unitCubeVolume :=
    Integrable.of_bound haM.aestronglyMeasurable ‖g‖ (ae_of_all _ fun _ => g.norm_coe_le_norm _)
  refine ⟨a,ha,?_⟩
  have hp : ∀ p : (I × I) × I, |g p-a (coordinateGridIndex n hnpos p)| ≤ eps/2 := by
    intro p
    have hh := hclose ((gridCubeLowerPoint_dist hnpos p).trans_lt hinv)
    exact (show |g p-a (coordinateGridIndex n hnpos p)| < eps/2 from hh).le
  have hfgInt : Integrable (fun p => |f p-g p|) unitCubeVolume := (hf.sub hg).abs
  have hfaInt : Integrable (fun p => |f p-a (coordinateGridIndex n hnpos p)|) unitCubeVolume := (hf.sub ha).abs
  calc
    (∫ p, |f p-a (coordinateGridIndex n hnpos p)| ∂unitCubeVolume)
        ≤ ∫ p, |f p-g p|+eps/2 ∂unitCubeVolume := by
          apply integral_mono hfaInt (hfgInt.add (integrable_const _))
          intro p
          dsimp only [Pi.add_apply]
          exact (abs_sub_le (f p) (g p) (a (coordinateGridIndex n hnpos p))).trans
            (add_le_add le_rfl (hp p))
    _ = (∫ p, |f p-g p| ∂unitCubeVolume)+eps/2 := by
      rw [integral_add hfgInt (integrable_const _),integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
    _ ≤ eps := by linarith only [hfg]

end LatinonEntropy

#print axioms LatinonEntropy.gridCubeLowerPoint_dist
#print axioms LatinonEntropy.exists_all_sizes_cube_grid_step_L1
