module

public import LatinBlockData
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology
open scoped Classical

def finiteTableEntropy {K : Type*} [Fintype K] (volume table : K → ℝ) : ℝ :=
  ∑ k, table k*Real.log (volume k/table k)

theorem mass_log_ratio_eq (v t : ℝ) (hv : v ≠ 0) :
    t*Real.log (v/t) = t*Real.log v-t*Real.log t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [Real.log_div hv ht]
    ring

/-- Positive reference volumes give continuity even when some target masses
vanish, through continuity of t log t at zero. -/
theorem finite_table_entropy_continuousAt {K : Type*} [Fintype K]
    (volume table : K → ℝ) (hv : ∀ k, 0 < volume k) :
    ContinuousAt (fun z : (K → ℝ) × (K → ℝ) => finiteTableEntropy z.1 z.2) (volume,table) := by
  have hcV : ∀ k, ContinuousAt (fun z : (K → ℝ) × (K → ℝ) => z.1 k) (volume,table) :=
    fun k => (continuous_apply k).continuousAt.comp continuous_fst.continuousAt
  have hcT : ∀ k, ContinuousAt (fun z : (K → ℝ) × (K → ℝ) => z.2 k) (volume,table) :=
    fun k => (continuous_apply k).continuousAt.comp continuous_snd.continuousAt
  have hs : ContinuousAt (fun z : (K → ℝ) × (K → ℝ) =>
      ∑ k, (z.2 k*Real.log (z.1 k)-z.2 k*Real.log (z.2 k))) (volume,table) :=
    tendsto_finsetSum univ (fun k _ =>
      ((hcT k).mul ((hcV k).log (hv k).ne')).sub
        (Real.continuous_mul_log.continuousAt.comp (hcT k)))
  have he : ∀ᶠ z : (K → ℝ) × (K → ℝ) in 𝓝 (volume,table), ∀ k, z.1 k ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    exact (hcV k).tendsto.eventually (eventually_ne_nhds (hv k).ne')
  apply hs.congr
  filter_upwards [he] with z hz
  unfold finiteTableEntropy
  apply sum_congr rfl
  intro k _
  exact (mass_log_ratio_eq (z.1 k) (z.2 k) (hz k)).symm

theorem finite_table_entropy_local_upper {K : Type*} [Fintype K]
    (volume table : K → ℝ) (hv : ∀ k, 0 < volume k) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ v t : K → ℝ,
      (∀ k, |v k-volume k| < delta) → (∀ k, |t k-table k| < delta) →
      finiteTableEntropy v t ≤ finiteTableEntropy volume table+eta := by
  obtain ⟨delta,hd,hclose⟩ := (Metric.continuousAt_iff.mp
    (finite_table_entropy_continuousAt volume table hv)) eta heta
  refine ⟨delta,hd,?_⟩
  intro v t hvclose htclose
  have hV : dist v volume < delta := (dist_pi_lt_iff hd).mpr
    (fun k => by simpa only [Real.dist_eq] using hvclose k)
  have hT : dist t table < delta := (dist_pi_lt_iff hd).mpr
    (fun k => by simpa only [Real.dist_eq] using htclose k)
  have hp : dist (v,t) (volume,table) < delta := by
    rw [Prod.dist_eq]
    exact max_lt hV hT
  have h := hclose hp
  change |finiteTableEntropy v t-finiteTableEntropy volume table| < eta at h
  have hu := (abs_lt.mp h).2
  linarith only [hu]

end LatinonEntropy
