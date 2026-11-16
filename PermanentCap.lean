module

public import LabelAveraging
public import PermanentCapScalar

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

theorem mean_log_remaining_le (hn : 0 < n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (s : ℝ) (hcap : ∀ i j, Q i j ≤ s)
    (sigma : Equiv.Perm (Fin n)) (hs : 0 < permWeight Q sigma) (i : Fin n) :
    finiteMean (fun lam : Fin n → Fin n => Real.log (remainingRowMass Q (labelKey lam) i sigma)) ≤
      finiteMean (fun t : Fin n => Real.log (s + ((n : ℝ) - t) / n)) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hpos : ∀ lam, 0 < remainingRowMass Q (labelKey lam) i sigma := by
    intro lam
    rw [remainingRowMass_owner_sum]
    apply lt_of_lt_of_le (positive_permWeight_entry Q hQ sigma hs i)
    have hle := single_le_sum
      (s := (univ : Finset (Fin n)))
      (f := fun k => if labelKey lam i ≤ labelKey lam k then Q i (sigma k) else 0)
      (fun k _ => by split_ifs <;> first | exact hQ i (sigma k) | exact le_rfl)
      (mem_univ i)
    simpa only [le_refl,ite_true] using hle
  rw [finiteMean_split i]
  apply finiteMean_mono
  intro t
  let f : ({k : Fin n // k ≠ i} → Fin n) → ℝ := fun rest =>
    remainingRowMass Q (labelKey ((Equiv.funSplitAt i (Fin n)).symm (t,rest))) i sigma
  have hf : ∀ rest, 0 < f rest := fun rest => hpos _
  have hmeanpos : 0 < finiteMean f :=
    div_pos (sum_pos (fun rest _ => hf rest) univ_nonempty) (Nat.cast_pos.mpr Fintype.card_pos)
  exact (finiteMean_log_le f hf).trans
    (Real.log_le_log hmeanpos (conditional_remaining_mean_le hn Q hQ hrow s hcap i sigma t))

/-- Capped-row permanent bound obtained directly by weighted revealing.
Only row stochasticity is required; no column hypothesis or Bregman
inequality is imported. The explicit error is O_m(log n). -/
theorem log_permanent_cap (hn : 0 < n) (m : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hper : 0 < Q.permanent)
    (hcap : ∀ i j, Q i j ≤ (m : ℝ) / n) :
    Real.log Q.permanent ≤ -(n : ℝ) + permanentCapError m n := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let B : ℝ := finiteMean (fun t : Fin n => Real.log ((m : ℝ) / n + ((n : ℝ) - t) / n))
  have hrowBound : ∀ sigma ∈ positivePermutations Q,
      finiteMean (fun lam : Fin n → Fin n => ∑ i,
        Real.log (remainingRowMass Q (labelKey lam) i sigma)) ≤ (n : ℝ) * B := by
    intro sigma hs
    rw [finiteMean_sum]
    calc
      _ ≤ ∑ _i : Fin n, B := sum_le_sum (fun i _ =>
        mean_log_remaining_le hn Q hQ hrow ((m : ℝ)/n) hcap sigma (mem_filter.mp hs).2 i)
      _ = _ := by simp
  have hmean := finiteMean_mono (fun lam : Fin n → Fin n =>
    log_permanent_remaining_mass Q hQ hper (labelKey lam) (labelKey_injective lam))
  rw [finiteMean_const,finiteMean_sum] at hmean
  simp_rw [finiteMean_mul] at hmean
  have hmass : (∑ sigma ∈ positivePermutations Q, permanentLaw Q sigma) = 1 := by
    simp only [permanentLaw]
    rw [← sum_div,sum_positive_permWeight Q hQ,div_self hper.ne']
  have htotal : (∑ sigma ∈ positivePermutations Q, permanentLaw Q sigma *
      finiteMean (fun lam : Fin n → Fin n => ∑ i,
        Real.log (remainingRowMass Q (labelKey lam) i sigma))) ≤ (n : ℝ) * B := by
    calc
      _ ≤ ∑ sigma ∈ positivePermutations Q, permanentLaw Q sigma * ((n : ℝ) * B) :=
        sum_le_sum (fun sigma hs => mul_le_mul_of_nonneg_left (hrowBound sigma hs)
          (permanentLaw_nonneg Q hQ hper sigma))
      _ = _ := by rw [← sum_mul,hmass,one_mul]
  exact (hmean.trans htotal).trans (finite_label_cap_sum n m hn)

theorem permanent_le_exp_cap (hn : 0 < n) (m : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcap : ∀ i j, Q i j ≤ (m : ℝ)/n) :
    Q.permanent ≤ Real.exp (-(n : ℝ)+permanentCapError m n) := by
  by_cases hper : 0 < Q.permanent
  · have h := Real.exp_le_exp.mpr (log_permanent_cap hn m Q hQ hrow hper hcap)
    rwa [Real.exp_log hper] at h
  · exact (le_of_not_gt hper).trans (Real.exp_pos _).le

end LatinonEntropy

#print axioms LatinonEntropy.log_permanent_cap
#print axioms LatinonEntropy.permanent_le_exp_cap
