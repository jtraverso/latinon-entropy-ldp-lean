module

public import UniformLatinonLocalUpper

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

theorem exists_fixed_prefactor_exp_square_bound (m : ℕ) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → (m : ℝ) ≤ Real.exp (gamma*(n : ℝ)^2) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (1/gamma)
  refine ⟨max (m+1) (K+1),by omega,?_⟩
  intro n hn
  have hm : m ≤ n := by omega
  have hkn : K < n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hknR : (K : ℝ) < n := by exact_mod_cast hkn
  have hlarge : 1 < gamma*(n : ℝ) := by
    have hh := (div_lt_iff₀ hgamma).mp (hK.trans hknR)
    nlinarith only [hh]
  have hmul := mul_le_mul_of_nonneg_right hlarge.le hnR
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hexp := Real.add_one_le_exp (gamma*(n : ℝ)^2)
  nlinarith only [hmul,hmn,hexp]

theorem exists_uniform_latinon_local_upper_below_rate (W : LatinonMeasure)
    (t : ℝ) (ht : ENNReal.ofReal t < latinonRate W) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W delta) ≤
        Real.exp ((n : ℝ)^2*(-t+eta)) := by
  by_cases htop : latinonRate W = ⊤
  · obtain ⟨delta,hd,N,hN,hp⟩ := exists_infinite_rate_uniform_latinon_local_upper W htop (t-eta)
    refine ⟨delta,hd,N,hN,?_⟩
    intro n hn
    have hh := hp n hn
    have he : -(n : ℝ)^2*(t-eta) = (n : ℝ)^2*(-t+eta) := by ring
    rwa [he] at hh
  · have hr : t < (latinonRate W).toReal := by
      rw [← ENNReal.ofReal_toReal htop] at ht
      exact (ENNReal.ofReal_lt_ofReal_iff'.mp ht).1
    obtain ⟨delta,hd,N,hN,hp⟩ := exists_finite_rate_uniform_latinon_local_upper W htop eta heta
    refine ⟨delta,hd,N,hN,?_⟩
    intro n hn
    apply (hp n hn).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [hr]) (sq_nonneg (n : ℝ))

/-- The actual uniform laws satisfy the upper bound on every compact set
in the full Latinon topology. Compactness of the entire space is separate. -/
theorem compact_uniform_latinon_upper (K : Set LatinonMeasure) (hK : IsCompact K)
    (t : ℝ) (ht : ∀ W ∈ K, ENNReal.ofReal t < latinonRate W) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real K ≤ Real.exp ((n : ℝ)^2*(-t+eps)) := by
  choose delta hd M hM hp using fun W : {W // W ∈ K} =>
    exists_uniform_latinon_local_upper_below_rate W.val t (ht W.val W.property) (eps/2) (half_pos heps)
  let U := fun W : {W // W ∈ K} => Metric.ball W.val (delta W)
  have hcover : K ⊆ ⋃ W, U W := by
    intro W hW
    apply Set.mem_iUnion.mpr
    exact ⟨⟨W,hW⟩,Metric.mem_ball_self (hd ⟨W,hW⟩)⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  obtain ⟨NA,hNA,habsorb⟩ := exists_fixed_prefactor_exp_square_bound F.card (eps/2) (half_pos heps)
  let N := max NA (F.sup M+1)
  have hN : 0 < N := hNA.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnA : NA ≤ n := (le_max_left _ _).trans hn
  let _ : IsProbabilityMeasure (uniformLatinonLaw (hN.trans_le hn)) := uniformLatinonLaw_probability _
  have hnF : F.sup M+1 ≤ n := (le_max_right _ _).trans hn
  have hnM : ∀ W ∈ F, M W ≤ n := by
    intro W hW
    have hh : M W ≤ F.sup M := Finset.le_sup hW
    omega
  calc
    (uniformLatinonLaw (hN.trans_le hn)).real K
        ≤ (uniformLatinonLaw (hN.trans_le hn)).real (⋃ W ∈ F, U W) :=
          measureReal_mono hF (measure_ne_top (uniformLatinonLaw (hN.trans_le hn)) _)
    _ ≤ ∑ W ∈ F, (uniformLatinonLaw (hN.trans_le hn)).real (U W) :=
      measureReal_biUnion_finset_le F U
    _ ≤ ∑ _W ∈ F, Real.exp ((n : ℝ)^2*(-t+eps/2)) := by
      apply sum_le_sum
      intro W hW
      exact hp W n (hnM W hW)
    _ = (F.card : ℝ)*Real.exp ((n : ℝ)^2*(-t+eps/2)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ Real.exp ((eps/2)*(n : ℝ)^2)*Real.exp ((n : ℝ)^2*(-t+eps/2)) :=
      mul_le_mul_of_nonneg_right (habsorb n hnA) (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ)^2*(-t+eps)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end LatinonEntropy

#print axioms LatinonEntropy.exists_fixed_prefactor_exp_square_bound
#print axioms LatinonEntropy.exists_uniform_latinon_local_upper_below_rate
#print axioms LatinonEntropy.compact_uniform_latinon_upper
