module

public import LatinonBridge.LaplaceBasics

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

theorem latinon_laplace_lower_at_point (phi : LatinonMeasure → ℝ) (hphi : Continuous phi)
    (W : LatinonMeasure) (hfinite : latinonRate W ≠ ⊤) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(phi W-(latinonRate W).toReal-eps)) ≤ latinonLaplace phi (hN.trans_le hn) := by
  let eta := eps/2
  have heta : 0 < eta := half_pos heps
  let U : Set LatinonMeasure := {V | phi W-eta < phi V}
  have hU : IsOpen U := isOpen_lt continuous_const hphi
  have hWU : W ∈ U := by change phi W-eta < phi W; linarith only [heta]
  obtain ⟨N,hN,hprob⟩ := open_uniform_latinon_lower_at_point U hU W hWU hfinite eta heta
  refine ⟨N,hN,?_⟩
  intro n hn
  let b := Real.exp ((n : ℝ)^2*(phi W-eta))
  have hi := integral_lower_of_event (uniformLatinonLaw (hN.trans_le hn))
    (fun V => Real.exp ((n : ℝ)^2*phi V)) (latinon_laplace_integrable phi hphi _)
    (fun _ => (Real.exp_pos _).le) U hU.measurableSet b (fun V hV =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hV) (sq_nonneg _)))
  calc
    Real.exp ((n : ℝ)^2*(phi W-(latinonRate W).toReal-eps)) =
        b*Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) := by
      dsimp [b]
      rw [← Real.exp_add]
      congr 1
      dsimp [eta]
      ring
    _ ≤ b*(uniformLatinonLaw (hN.trans_le hn)).real U :=
      mul_le_mul_of_nonneg_left (hprob n hn) (Real.exp_pos _).le
    _ ≤ latinonLaplace phi (hN.trans_le hn) := hi

/-- Compact-space Laplace upper bound. Infinite-rate points are retained;
only finite-rate points occur in the variational comparison hypothesis. -/
theorem latinon_laplace_upper_of_variational_bound (phi : LatinonMeasure → ℝ) (hphi : Continuous phi)
    (s : ℝ) (hs : ∀ W, latinonRate W ≠ ⊤ → phi W-(latinonRate W).toReal ≤ s)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      latinonLaplace phi (hN.trans_le hn) ≤ Real.exp ((n : ℝ)^2*(s+eps)) := by
  let eta := eps/4
  have heta : 0 < eta := by dsimp [eta]; positivity
  let U : LatinonMeasure → Set LatinonMeasure := fun W => {V | phi W-eta < phi V ∧ phi V < phi W+eta}
  let C : LatinonMeasure → Set LatinonMeasure := fun W => {V | phi W-eta ≤ phi V ∧ phi V ≤ phi W+eta}
  have hU (W : LatinonMeasure) : IsOpen (U W) :=
    (isOpen_lt continuous_const hphi).inter (isOpen_lt hphi continuous_const)
  have hC (W : LatinonMeasure) : IsClosed (C W) :=
    (isClosed_le continuous_const hphi).inter (isClosed_le hphi continuous_const)
  have hcover : (Set.univ : Set LatinonMeasure) ⊆ ⋃ W, U W := by
    intro W _
    apply Set.mem_iUnion.mpr
    refine ⟨W,?_,?_⟩ <;> linarith only [heta]
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let t : LatinonMeasure → ℝ := fun W => phi W-eta-s
  have hRate (W V : LatinonMeasure) (hV : V ∈ C W) : ENNReal.ofReal (t W) ≤ latinonRate V := by
    by_cases htop : latinonRate V=⊤
    · rw [htop]
      exact le_top
    · have hb := hs V htop
      have ht : t W ≤ (latinonRate V).toReal := by dsimp [t]; linarith only [hV.1,hb]
      rw [← ENNReal.ofReal_toReal htop]
      exact ENNReal.ofReal_le_ofReal ht
  choose M hM hp using (fun W => closed_uniform_latinon_upper (C W) (hC W) (t W) (hRate W) eta heta)
  obtain ⟨A,hA,habsorb⟩ := exists_fixed_prefactor_exp_square_bound F.card eta heta
  let N := max A (F.sup M+1)
  have hN : 0 < N := hA.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnA : A ≤ n := (le_max_left _ _).trans hn
  have hnF : F.sup M+1 ≤ n := (le_max_right _ _).trans hn
  have hnM (W : LatinonMeasure) (hW : W ∈ F) : M W ≤ n := by
    have hh : M W ≤ F.sup M := Finset.le_sup hW
    omega
  let b : LatinonMeasure → ℝ := fun W => Real.exp ((n : ℝ)^2*(phi W+eta))
  have hfiniteCover (V : LatinonMeasure) : ∃ W ∈ F, V ∈ C W := by
    obtain ⟨W,hWV⟩ := Set.mem_iUnion.mp (hF (Set.mem_univ V))
    obtain ⟨hWF,hVU⟩ := Set.mem_iUnion.mp hWV
    exact ⟨W,hWF,hVU.1.le,hVU.2.le⟩
  have hcap (W : LatinonMeasure) (_ : W ∈ F) (V : LatinonMeasure) (hV : V ∈ C W) :
      Real.exp ((n : ℝ)^2*phi V) ≤ b W :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV.2 (sq_nonneg _))
  have hi := integral_upper_of_finite_cover (uniformLatinonLaw (hN.trans_le hn))
    (fun V => Real.exp ((n : ℝ)^2*phi V)) (latinon_laplace_integrable phi hphi _) F C
    (fun W _ => (hC W).measurableSet) b (fun W _ => (Real.exp_pos _).le) hfiniteCover hcap
  calc
    latinonLaplace phi (hN.trans_le hn) ≤ ∑ W ∈ F, b W*(uniformLatinonLaw (hN.trans_le hn)).real (C W) := hi
    _ ≤ ∑ W ∈ F, b W*Real.exp ((n : ℝ)^2*(-t W+eta)) := by
      apply Finset.sum_le_sum
      intro W hW
      exact mul_le_mul_of_nonneg_left (hp W n (hnM W hW)) (Real.exp_pos _).le
    _ = ∑ _W ∈ F, Real.exp ((n : ℝ)^2*(s+3*eta)) := by
      apply Finset.sum_congr rfl
      intro W _
      change Real.exp ((n : ℝ)^2*(phi W+eta))*Real.exp ((n : ℝ)^2*(-t W+eta))=_
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    _ = (F.card : ℝ)*Real.exp ((n : ℝ)^2*(s+3*eta)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ Real.exp (eta*(n : ℝ)^2)*Real.exp ((n : ℝ)^2*(s+3*eta)) :=
      mul_le_mul_of_nonneg_right (habsorb n hnA) (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ)^2*(s+eps)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [eta]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.latinon_laplace_lower_at_point
#print axioms LatinonEntropy.latinon_laplace_upper_of_variational_bound
