module

public import WeightedChain
public import PermanentalLaw

@[expose] public section

/-! Apply weighted revealing to the permanent, retaining all row weights.
The remaining averaging over random row orders is a separate theorem. -/

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

def positivePermutations (Q : Matrix (Fin n) (Fin n) ℝ) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun sigma => 0 < permWeight Q sigma)

theorem positivePermutations_nonempty (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent) : (positivePermutations Q).Nonempty := by
  obtain ⟨sigma,hs⟩ := exists_positive_permWeight Q hQ hper
  exact ⟨sigma,mem_filter.mpr ⟨mem_univ _,hs⟩⟩

theorem positive_permWeight_entry (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (sigma : Equiv.Perm (Fin n))
    (hs : 0 < permWeight Q sigma) (i : Fin n) : 0 < Q i (sigma i) := by
  have hp : (∏ j, Q j (sigma j)) ≠ 0 := hs.ne'
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (mem_univ i)
  exact lt_of_le_of_ne (hQ i (sigma i)) hi.symm

theorem log_positive_permWeight (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (sigma : Equiv.Perm (Fin n))
    (hs : 0 < permWeight Q sigma) :
    Real.log (permWeight Q sigma) = ∑ i, Real.log (Q i (sigma i)) := by
  unfold permWeight
  exact Real.log_prod (fun i _ => (positive_permWeight_entry Q hQ sigma hs i).ne')

theorem sum_positive_permWeight (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) : (∑ sigma ∈ positivePermutations Q, permWeight Q sigma) = Q.permanent := by
  rw [← sum_permWeight Q]
  simp only [positivePermutations, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro sigma _
  split_ifs with hs
  · rfl
  · have hz := le_antisymm (le_of_not_gt hs) (permWeight_nonneg Q hQ sigma)
    simp [hz]

theorem log_permanent_weighted_reveal (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent)
    (key : Fin n → ℕ) (hkey : Function.Injective key) :
    Real.log Q.permanent ≤
      ∑ sigma ∈ positivePermutations Q, permanentLaw Q sigma *
        ∑ i, Real.log (availableReference (positivePermutations Q) univ key
          (fun i tau => tau i) (fun i j => Q i j) i sigma) := by
  classical
  let S := positivePermutations Q
  have hw : ∀ sigma ∈ S, 0 < permWeight Q sigma := fun sigma hs => (mem_filter.mp hs).2
  have hc := weighted_chain_bound key (fun i (tau : Equiv.Perm (Fin n)) => tau i)
    (permWeight Q) (fun i j => Q i j) univ S
    (fun _ _ _ _ h => hkey h)
    (fun sigma _ tau _ h => Equiv.ext (fun i => h i (mem_univ i)))
    (positivePermutations_nonempty Q hQ hper) hw
    (fun i _ sigma hs => positive_permWeight_entry Q hQ sigma (hw sigma hs) i)
  have he :
      (∑ sigma ∈ S, permWeight Q sigma * ∑ i,
        (Real.log (availableReference S univ key (fun i tau => tau i) (fun i j => Q i j) i sigma) -
          Real.log (Q i (sigma i)))) =
      (∑ sigma ∈ S, permWeight Q sigma * ∑ i,
        Real.log (availableReference S univ key (fun i tau => tau i) (fun i j => Q i j) i sigma)) -
      ∑ sigma ∈ S, permWeight Q sigma * Real.log (permWeight Q sigma) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro sigma hs
    rw [Finset.sum_sub_distrib,mul_sub,log_positive_permWeight Q hQ sigma (hw sigma hs)]
  unfold weightedFamilyEntropy at hc
  rw [sum_positive_permWeight Q hQ,he] at hc
  have hscaled : Q.permanent * Real.log Q.permanent ≤
      ∑ sigma ∈ S, permWeight Q sigma * ∑ i,
        Real.log (availableReference S univ key (fun i tau => tau i) (fun i j => Q i j) i sigma) := by
    linarith
  calc
    Real.log Q.permanent ≤
        (∑ sigma ∈ S, permWeight Q sigma * ∑ i,
          Real.log (availableReference S univ key (fun i tau => tau i) (fun i j => Q i j) i sigma)) /
          Q.permanent := (le_div_iff₀ hper).mpr (by nlinarith)
    _ = _ := by
      simp only [permanentLaw,div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro sigma _
      ring

def remainingRowMass (Q : Matrix (Fin n) (Fin n) ℝ) (key : Fin n → ℕ)
    (i : Fin n) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ j ∈ univ.filter (fun j => key i ≤ key (sigma.symm j)), Q i j

theorem availableReference_le_remainingRowMass
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (key : Fin n → ℕ) (i : Fin n) (sigma : Equiv.Perm (Fin n)) :
    availableReference (positivePermutations Q) univ key
      (fun i tau => tau i) (fun i j => Q i j) i sigma ≤ remainingRowMass Q key i sigma := by
  classical
  unfold availableReference remainingRowMass
  apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hQ i j)
  intro j hj
  obtain ⟨tau,htau,hj⟩ := mem_image.mp hj
  simp only [revealFibre, mem_filter] at htau
  have hpref := htau.2
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  by_contra hn
  have hbefore : key (sigma.symm j) < key i := lt_of_not_ge hn
  have he := hpref (sigma.symm j) (mem_univ _) hbefore
  have heq : tau (sigma.symm j) = tau i :=
    (he.trans (sigma.apply_symm_apply j)).trans hj.symm
  have hsame := tau.injective heq
  rw [hsame] at hbefore
  exact (lt_irrefl _ hbefore)

theorem availableReference_perm_pos
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (key : Fin n → ℕ) (i : Fin n) (sigma : Equiv.Perm (Fin n))
    (hs : sigma ∈ positivePermutations Q) :
    0 < availableReference (positivePermutations Q) univ key
      (fun i tau => tau i) (fun i j => Q i j) i sigma := by
  classical
  have hself : sigma ∈ revealFibre (positivePermutations Q) univ key
      (fun i tau => tau i) i sigma := by
    simp [revealFibre, hs]
  have hm := mem_image_of_mem (fun tau : Equiv.Perm (Fin n) => tau i) hself
  exact lt_of_lt_of_le
    (positive_permWeight_entry Q hQ sigma (mem_filter.mp hs).2 i)
    (Finset.single_le_sum (fun j _ => hQ i j) hm)

/-- A genuine upper bound on the permanent, still indexed by one deterministic
row order. Averaging these orders is the remaining cap-bound step. -/
theorem log_permanent_remaining_mass (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent)
    (key : Fin n → ℕ) (hkey : Function.Injective key) :
    Real.log Q.permanent ≤
      ∑ sigma ∈ positivePermutations Q, permanentLaw Q sigma *
        ∑ i, Real.log (remainingRowMass Q key i sigma) := by
  apply (log_permanent_weighted_reveal Q hQ hper key hkey).trans
  apply Finset.sum_le_sum
  intro sigma hs
  apply mul_le_mul_of_nonneg_left ?_ (permanentLaw_nonneg Q hQ hper sigma)
  apply Finset.sum_le_sum
  intro i _
  exact Real.log_le_log (availableReference_perm_pos Q hQ key i sigma hs)
    (availableReference_le_remainingRowMass Q hQ key i sigma)

end LatinonEntropy

#print axioms LatinonEntropy.log_permanent_weighted_reveal
#print axioms LatinonEntropy.log_permanent_remaining_mass
