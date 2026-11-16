module

public import LatinonBridge.LatinonGlobalDeviations
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

theorem exists_latinon_continuous_upper (phi : LatinonMeasure → ℝ) (hphi : Continuous phi) :
    ∃ B : ℝ, ∀ W, phi W ≤ B := by
  have hb : BddAbove (Set.range phi) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hphi).bddAbove
  obtain ⟨B,hB⟩ := hb
  exact ⟨B,fun W => hB ⟨W,rfl⟩⟩

def latinonLaplace (phi : LatinonMeasure → ℝ) {n : ℕ} (hn : 0 < n) : ℝ :=
  ∫ W, Real.exp ((n : ℝ)^2*phi W) ∂uniformLatinonLaw hn

theorem latinon_laplace_integrable (phi : LatinonMeasure → ℝ) (hphi : Continuous phi)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun W => Real.exp ((n : ℝ)^2*phi W)) (uniformLatinonLaw hn) := by
  obtain ⟨B,hB⟩ := exists_latinon_continuous_upper phi hphi
  have hm : Measurable (fun W => Real.exp ((n : ℝ)^2*phi W)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hphi.measurable)
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp ((n : ℝ)^2*B))
  apply ae_of_all
  intro W
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB W) (sq_nonneg _))

theorem integral_lower_of_event {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (g : X → ℝ) (hg : Integrable g mu)
    (hg0 : ∀ x, 0 ≤ g x) (C : Set X) (hC : MeasurableSet C) (b : ℝ)
    (hcap : ∀ x ∈ C, b ≤ g x) : b*mu.real C ≤ ∫ x, g x ∂mu := by
  have hi : Integrable (C.indicator (fun _ => b)) mu := (integrable_const _).indicator hC
  calc
    b*mu.real C = ∫ x, C.indicator (fun _ => b) x ∂mu := by
      rw [integral_indicator_const b hC,smul_eq_mul,mul_comm]
    _ ≤ ∫ x, g x ∂mu := by
      apply integral_mono hi hg
      intro x
      by_cases hx : x ∈ C
      · rw [Set.indicator_of_mem hx]
        exact hcap x hx
      · rw [Set.indicator_of_notMem hx]
        exact hg0 x

theorem integral_upper_of_finite_cover {X A : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (g : X → ℝ) (hg : Integrable g mu)
    (F : Finset A) (C : A → Set X) (hC : ∀ i ∈ F, MeasurableSet (C i))
    (b : A → ℝ) (hb : ∀ i ∈ F, 0 ≤ b i)
    (hcover : ∀ x, ∃ i ∈ F, x ∈ C i) (hcap : ∀ i ∈ F, ∀ x ∈ C i, g x ≤ b i) :
    (∫ x, g x ∂mu) ≤ ∑ i ∈ F, b i*mu.real (C i) := by
  have hi (i : A) (hif : i ∈ F) : Integrable ((C i).indicator (fun _ => b i)) mu :=
    (integrable_const _).indicator (hC i hif)
  have hp (x : X) : g x ≤ ∑ i ∈ F, (C i).indicator (fun _ => b i) x := by
    obtain ⟨i,hif,hxi⟩ := hcover x
    calc
      g x ≤ b i := hcap i hif x hxi
      _ = (C i).indicator (fun _ => b i) x := by rw [Set.indicator_of_mem hxi]
      _ ≤ _ := Finset.single_le_sum (s := F) (f := fun j => (C j).indicator (fun _ => b j) x) (fun j hj => by
        by_cases hxj : x ∈ C j
        · rw [Set.indicator_of_mem hxj]
          exact hb j hj
        · rw [Set.indicator_of_notMem hxj]) hif
  calc
    (∫ x, g x ∂mu) ≤ ∫ x, ∑ i ∈ F, (C i).indicator (fun _ => b i) x ∂mu :=
      integral_mono hg (integrable_finsetSum F hi) hp
    _ = ∑ i ∈ F, ∫ x, (C i).indicator (fun _ => b i) x ∂mu := integral_finsetSum F hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hif
      rw [integral_indicator_const (b i) (hC i hif),smul_eq_mul,mul_comm]

end LatinonEntropy

#print axioms LatinonEntropy.exists_latinon_continuous_upper
#print axioms LatinonEntropy.latinon_laplace_integrable
#print axioms LatinonEntropy.integral_lower_of_event
#print axioms LatinonEntropy.integral_upper_of_finite_cover
