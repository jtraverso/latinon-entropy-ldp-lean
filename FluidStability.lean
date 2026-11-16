module

public import WeightedJensen
public import Mathlib.Analysis.ODE.DiscreteGronwall

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def propagationKernel (H : ℕ → ℝ) (s t : ℕ) : ℝ :=
  ∏ k ∈ Ico (s+1) t, (1-H k)

theorem propagationKernel_bounds (H : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k ∧ H k ≤ 1) (s t : ℕ) :
    0 ≤ propagationKernel H s t ∧ propagationKernel H s t ≤ 1 := by
  constructor
  · exact prod_nonneg (fun k _ => by linarith [(hH k).2])
  · exact Finset.prod_le_one₀ (fun k _ => by linarith [(hH k).2]) (fun k _ => by linarith [(hH k).1])

theorem fluid_defect_telescope (H E D : ℕ → ℝ) (hzero : D 0 = 0)
    (hstep : ∀ t, D (t+1) = D t*(1-H t)-E t) (t : ℕ) :
    D t = -(∑ s ∈ range t, propagationKernel H s t*E s) := by
  induction t with
  | zero => simpa using hzero
  | succ t ih =>
    have hk : ∀ s ∈ range t, propagationKernel H s (t+1) =
        propagationKernel H s t*(1-H t) := by
      intro s hs
      exact prod_Ico_succ_top (by have := mem_range.mp hs; omega) _
    have hlast : propagationKernel H t (t+1) = 1 := by simp [propagationKernel]
    have hsum : (∑ s ∈ range t, propagationKernel H s (t+1)*E s) =
        (∑ s ∈ range t, propagationKernel H s t*E s)*(1-H t) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro s hs
      rw [hk s hs]
      ring
    rw [hstep,ih,sum_range_succ,hsum,hlast]
    ring

/-- Gronwall for the precise defect-envelope shape used by C3. The separate
task of deriving this recurrence from the stopped process remains explicit. -/
theorem defect_gronwall (D : ℕ → ℝ) (A b B L : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hrec : ∀ t, D t ≤ A+b*(∑ s ∈ range t, (B+L*D s))) (t : ℕ) :
    D t ≤ (A+(t : ℝ)*b*B)*Real.exp ((t : ℝ)*b*L) := by
  let g : ℕ → ℝ := fun t => A+b*(∑ s ∈ range t, (B+L*D s))
  have hD : ∀ t, D t ≤ g t := hrec
  have hg : ∀ t, g (t+1) = g t+b*(B+L*D t) := by
    intro t
    simp only [g,sum_range_succ]
    ring
  have hstep : ∀ t ≥ 0, g (t+1) ≤ (1+b*L)*g t+b*B := by
    intro t _
    have hm := mul_le_mul_of_nonneg_left (hD t) (mul_nonneg hb hL)
    rw [hg]
    nlinarith only [hm]
  have hbound := discrete_gronwall (u := g) (b := fun _ => b*B) (c := fun _ => b*L)
    (n₀ := 0) (by simpa [g] using hA) hstep
    (fun _ _ => mul_nonneg hb hL) (fun _ _ => mul_nonneg hb hB) (n := t) (Nat.zero_le t)
  have hbound' : g t ≤ (A+(t : ℝ)*b*B)*Real.exp ((t : ℝ)*b*L) := by
    simpa [g,mul_assoc] using hbound
  exact (hD t).trans hbound'

end LatinonEntropy

#print axioms LatinonEntropy.fluid_defect_telescope
#print axioms LatinonEntropy.defect_gronwall
