module

public import LatinBipartiteFactorizations
public import CDRLatinBlockTransfer

@[expose] public section

/-! Entropy transfer for finitely many distinguished Latin blocks. The order
threshold is chosen before the finite completion layout and the ambient STS.
The conclusion counts actual block sets, with no division by a fibre bound. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem finite_rate_latin_block_product_lower {J : Type*} [Fintype J]
    (W : J → LatinonMeasure) (hfinite : ∀ j, latinonRate (W j) ≠ ⊤)
    (rho eta : ℝ) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal-eta)) ≤
        ∏ j, ((latinonBallLatinFamily (hN.trans_le hn) (W j) rho).card : ℝ) := by
  choose N hN hcount using fun j =>
    finite_rate_latinon_fixed_target_count_lower (W j) (hfinite j) rho eta hrho heta
  let M := 1 + ∑ j, N j
  have hM : 0 < M := by dsimp [M]; omega
  have hNj : ∀ j, N j ≤ M := by
    intro j
    exact (single_le_sum (fun i _ => Nat.zero_le (N i)) (mem_univ j)).trans (by dsimp [M]; omega)
  refine ⟨M,hM,?_⟩
  intro n hn
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
    (fun j _ => hcount j n ((hNj j).trans hn))

namespace CDRLatinBlockTemplate

variable {J V : Type*} [Fintype J] [DecidableEq V] {n : ℕ} {col : V → Fin 3}

/-- Every counted element is an actual CDR realization, and each local square
lies in its prescribed full-metric Latinon ball. -/
theorem restrictedRealizations_profile (T : CDRLatinBlockTemplate J V n col)
    (S : CDRBicolour.STS V) (Λ₀ : J → LatinArray n) (hbase : T.packing Λ₀ ⊆ S.blocks)
    (hS : CDRBicolour.IsStrictBicolouring S col) (hn : 0 < n)
    (W : J → LatinonMeasure) (rho : ℝ) {B : Finset (Finset V)}
    (hB : B ∈ T.restrictedRealizations S Λ₀ hbase (fun j => latinonBallLatinFamily hn (W j) rho)) :
    ∃ (S' : CDRBicolour.STS V) (Λ : J → LatinArray n),
      S'.blocks = B ∧ CDRBicolour.IsStrictBicolouring S' col ∧
      (∀ j, dist (latinArrayToLatinonMeasure hn (Λ j)) (W j) < rho) ∧
      S'.blocks = (S.blocks \ T.packing Λ₀) ∪ T.packing Λ := by
  obtain ⟨Λ,hΛ,rfl⟩ := T.mem_restrictedRealizations S Λ₀ hbase _ hB
  refine ⟨T.completed S Λ₀ hbase Λ,Λ,rfl,T.completed_bicoloured S Λ₀ hbase hS Λ,?_,rfl⟩
  intro j
  exact (mem_filter.mp (hΛ j)).2

end CDRLatinBlockTemplate

/-- Both exponential bounds, with the radius of each block chosen before n.
This is an exact product count, so no completion entropy is discarded. -/
theorem finite_rate_latin_block_product_entropy_count {J : Type*} [Fintype J]
    (W : J → LatinonMeasure) (hfinite : ∀ j, latinonRate (W j) ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : J → ℝ, (∀ j, 0 < rho j ∧ rho j ≤ r) ∧
      ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal-eta)) ≤
        ∏ j, ((latinonBallLatinFamily (hN.trans_le hn) (W j) (rho j)).card : ℝ) ∧
      (∏ j, ((latinonBallLatinFamily (hN.trans_le hn) (W j) (rho j)).card : ℝ)) ≤
        Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal+eta)) := by
  choose rho hrho hror N hN hcount using fun j =>
    finite_rate_latinon_entropy_count (W j) (hfinite j) r eta hr heta
  let M := 1 + ∑ j, N j
  have hM : 0 < M := by dsimp [M]; omega
  have hNj : ∀ j, N j ≤ M := by
    intro j
    exact (single_le_sum (fun i _ => Nat.zero_le (N i)) (mem_univ j)).trans (by dsimp [M]; omega)
  refine ⟨rho,fun j => ⟨hrho j,hror j⟩,M,hM,?_⟩
  intro n hn
  constructor
  · rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun j _ => (hcount j n ((hNj j).trans hn)).1)
  · rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun j _ => (hcount j n ((hNj j).trans hn)).2)

/-- Lower entropy count inside any fixed completed switchable CDR layout.
The completion is the fixed residual of the supplied base system. The theorem
does not count all CDR systems or prescribe an arbitrary global AAC count. -/
theorem cdr_distinguished_latinon_blocks_lower {J : Type*} [Fintype J]
    (W : J → LatinonMeasure) (hfinite : ∀ j, latinonRate (W j) ≠ ⊤)
    (rho eta : ℝ) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∀ {V : Type*} [DecidableEq V] (col : V → Fin 3)
        (T : CDRLatinBlockTemplate J V n col) (S : CDRBicolour.STS V)
        (Λ₀ : J → LatinArray n) (hbase : T.packing Λ₀ ⊆ S.blocks),
      Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal-eta)) ≤
        ((T.restrictedRealizations S Λ₀ hbase
          (fun j => latinonBallLatinFamily (hN.trans_le hn) (W j) rho)).card : ℝ) := by
  obtain ⟨N,hN,hcount⟩ := finite_rate_latin_block_product_lower W hfinite rho eta hrho heta
  refine ⟨N,hN,?_⟩
  intro n hn V _ col T S Λ₀ hbase
  rw [T.card_restrictedRealizations S Λ₀ hbase, Nat.cast_prod]
  exact hcount n hn

/-- Sharp local count in the explicitly constructed family of CDR block sets.
The given base system is strictly bicoloured, and every counted output is
certified to have that property. -/
theorem cdr_distinguished_latinon_blocks_entropy_count {J : Type*} [Fintype J]
    (W : J → LatinonMeasure) (hfinite : ∀ j, latinonRate (W j) ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : J → ℝ, (∀ j, 0 < rho j ∧ rho j ≤ r) ∧
      ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∀ {V : Type*} [DecidableEq V] (col : V → Fin 3)
        (T : CDRLatinBlockTemplate J V n col) (S : CDRBicolour.STS V)
        (_hS : CDRBicolour.IsStrictBicolouring S col)
        (Λ₀ : J → LatinArray n) (hbase : T.packing Λ₀ ⊆ S.blocks),
      let A := fun j => latinonBallLatinFamily (hN.trans_le hn) (W j) (rho j)
      (Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal-eta)) ≤
        ((T.restrictedRealizations S Λ₀ hbase A).card : ℝ) ∧
      ((T.restrictedRealizations S Λ₀ hbase A).card : ℝ) ≤
        Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal+eta))) ∧
      ∀ B ∈ T.restrictedRealizations S Λ₀ hbase A,
        ∃ S' : CDRBicolour.STS V, S'.blocks = B ∧ CDRBicolour.IsStrictBicolouring S' col := by
  obtain ⟨rho,hrho,N,hN,hcount⟩ := finite_rate_latin_block_product_entropy_count W hfinite r eta hr heta
  refine ⟨rho,hrho,N,hN,?_⟩
  intro n hn V _ col T S hS Λ₀ hbase
  constructor
  · simpa only [T.card_restrictedRealizations S Λ₀ hbase,Nat.cast_prod] using hcount n hn
  · intro B hB
    obtain ⟨Λ,-,rfl⟩ := T.mem_restrictedRealizations S Λ₀ hbase _ hB
    exact ⟨T.completed S Λ₀ hbase Λ,rfl,T.completed_bicoloured S Λ₀ hbase hS Λ⟩

end LatinonEntropy

#print axioms LatinonEntropy.finite_rate_latin_block_product_lower
#print axioms LatinonEntropy.CDRLatinBlockTemplate.restrictedRealizations_profile
#print axioms LatinonEntropy.cdr_distinguished_latinon_blocks_lower
#print axioms LatinonEntropy.finite_rate_latin_block_product_entropy_count
#print axioms LatinonEntropy.cdr_distinguished_latinon_blocks_entropy_count
