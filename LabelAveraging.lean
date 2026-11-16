module

public import FiniteAverages
public import PermanentReveal

@[expose] public section

/-! Independent finite labels produce an injective row order. The averaging
step retains the chosen entry and averages only the other row owners. -/

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

def labelKey (lam : Fin n → Fin n) (i : Fin n) : ℕ := (lam i : ℕ) * n + i

theorem labelKey_injective (lam : Fin n → Fin n) : Function.Injective (labelKey lam) := by
  intro i j h
  have hm := congrArg (fun k => k % n) h
  simp only [labelKey,Nat.mul_add_mod_of_lt i.isLt,Nat.mul_add_mod_of_lt j.isLt] at hm
  exact Fin.ext hm

theorem label_le_of_key_le (lam : Fin n → Fin n) (i j : Fin n)
    (h : labelKey lam i ≤ labelKey lam j) : lam i ≤ lam j := by
  by_contra hn
  have hv : (lam j : ℕ) + 1 ≤ lam i := by exact Nat.succ_le_of_lt (Fin.lt_def.mp (lt_of_not_ge hn))
  have hj := j.isLt
  unfold labelKey at h
  nlinarith

theorem finiteMean_label_ge (t : Fin n) (w : ℝ) :
    finiteMean (fun u : Fin n => if t ≤ u then w else 0) =
      ((n : ℝ) - t) / n * w := by
  unfold finiteMean
  rw [← sum_filter]
  have he : univ.filter (fun u : Fin n => t ≤ u) = Ici t := by ext; simp
  rw [he,sum_const,Fin.card_Ici,Fintype.card_fin,nsmul_eq_mul]
  rw [Nat.cast_sub (le_of_lt t.isLt)]
  ring

theorem remainingRowMass_owner_sum (Q : Matrix (Fin n) (Fin n) ℝ)
    (key : Fin n → ℕ) (i : Fin n) (sigma : Equiv.Perm (Fin n)) :
    remainingRowMass Q key i sigma =
      ∑ k, if key i ≤ key k then Q i (sigma k) else 0 := by
  unfold remainingRowMass
  rw [sum_filter]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp sigma (fun j => if key i ≤ key (sigma.symm j) then Q i j else 0)).symm

theorem conditional_remaining_mean_le (hn : 0 < n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (s : ℝ) (hcap : ∀ i j, Q i j ≤ s)
    (i : Fin n) (sigma : Equiv.Perm (Fin n)) (t : Fin n) :
    finiteMean (fun rest : {k : Fin n // k ≠ i} → Fin n =>
      remainingRowMass Q (labelKey ((Equiv.funSplitAt i (Fin n)).symm (t,rest))) i sigma) ≤
      s + ((n : ℝ) - t) / n := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let assemble (rest : {k : Fin n // k ≠ i} → Fin n) :=
    (Equiv.funSplitAt i (Fin n)).symm (t,rest)
  let p : ℝ := ((n : ℝ) - t) / n
  have htR : (t : ℝ) ≤ n := by exact_mod_cast (le_of_lt t.isLt)
  have hp : 0 ≤ p := div_nonneg (by linarith) (Nat.cast_nonneg n)
  have hi : ∀ rest, assemble rest i = t := by
    intro rest
    simp [assemble,Equiv.funSplitAt_symm_apply]
  have ho : ∀ rest k (hk : k ≠ i), assemble rest k = rest ⟨k,hk⟩ := by
    intro rest k hk
    simp [assemble,Equiv.funSplitAt_symm_apply,hk]
  let other (k : Fin n) (rest : {k : Fin n // k ≠ i} → Fin n) : ℝ :=
    if k = i then 0 else if t ≤ assemble rest k then Q i (sigma k) else 0
  have havg : ∀ k, finiteMean (other k) = if k = i then 0 else p * Q i (sigma k) := by
    intro k
    by_cases hk : k = i
    · subst k
      simp [other,finiteMean_const]
    · have he : other k = fun rest => if t ≤ rest ⟨k,hk⟩ then Q i (sigma k) else 0 := by
        funext rest
        simp [other,hk,ho]
      rw [he]
      have hc := finiteMean_coordinate (V := {k : Fin n // k ≠ i})
        (B := Fin n) ⟨k,hk⟩ (fun u => if t ≤ u then Q i (sigma k) else 0)
      rw [hc,finiteMean_label_ge]
      simp [hk,p]
  have hpoint : ∀ rest, remainingRowMass Q (labelKey (assemble rest)) i sigma ≤
      Q i (sigma i) + ∑ k, other k rest := by
    intro rest
    rw [remainingRowMass_owner_sum]
    calc
      (∑ k, if labelKey (assemble rest) i ≤ labelKey (assemble rest) k then Q i (sigma k) else 0) ≤
          ∑ k, ((if k = i then Q i (sigma i) else 0) + other k rest) := by
        apply sum_le_sum
        intro k _
        by_cases hk : k = i
        · subst k
          simp [other]
        · simp only [hk,ite_false,zero_add,other]
          split_ifs with hbefore hlab hlab
          · rfl
          · have he := label_le_of_key_le (assemble rest) i k hbefore
            rw [hi] at he
            exact False.elim (hlab he)
          · exact hQ i (sigma k)
          · exact le_rfl
      _ = _ := by simp [sum_add_distrib]
  have hmean := finiteMean_mono hpoint
  rw [finiteMean_add,finiteMean_const,finiteMean_sum] at hmean
  simp_rw [havg] at hmean
  have hsum : (∑ k, if k = i then (0 : ℝ) else p * Q i (sigma k)) ≤ p := by
    calc
      _ ≤ ∑ k, p * Q i (sigma k) := by
        apply sum_le_sum
        intro k _
        split_ifs
        · exact mul_nonneg hp (hQ i (sigma k))
        · exact le_rfl
      _ = p := by rw [← mul_sum,Equiv.sum_comp sigma,hrow,mul_one]
  change finiteMean (fun rest => remainingRowMass Q (labelKey (assemble rest)) i sigma) ≤ s + p
  linarith [hcap i (sigma i)]

end LatinonEntropy

#print axioms LatinonEntropy.conditional_remaining_mean_le
