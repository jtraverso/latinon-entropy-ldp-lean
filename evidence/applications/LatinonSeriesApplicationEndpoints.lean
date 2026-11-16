module

public import DistinguishedBlockEntropy
public import WilsonLatinBlockTemplate

@[expose] public section

/-! Additive public entry for the two applications. The original C1--C7
entry and its source snapshot remain frozen. -/

noncomputable section

namespace LatinonEntropy

open Finset CDRBicolour.Absorption.Count.Wilson CDRBicolour.Prefix
open scoped Classical

def wilsonProfileRealizations {a b c g n : ℕ} {G : Finset (Finset (Fin g))}
    (h : WCond a b c g n) (hG : STS.IsSTS G)
    (S : CDRBicolour.STS (Fin (a+b+c))) (Λ₀ : Ix G → LatinArray n)
    (hbase : crossP h Λ₀ ⊆ S.blocks) (hn : 0 < n)
    (W : Ix G → LatinonMeasure) (rho : Ix G → ℝ) : Finset (Finset (Finset (Fin (a+b+c)))) :=
  (wilsonLatinBlockTemplate h hG).restrictedRealizations S Λ₀ hbase
    (fun j => latinonBallLatinFamily hn (W j) (rho j))

theorem card_wilsonProfileRealizations {a b c g n : ℕ} {G : Finset (Finset (Fin g))}
    (h : WCond a b c g n) (hG : STS.IsSTS G)
    (S : CDRBicolour.STS (Fin (a+b+c))) (Λ₀ : Ix G → LatinArray n)
    (hbase : crossP h Λ₀ ⊆ S.blocks) (hn : 0 < n)
    (W : Ix G → LatinonMeasure) (rho : Ix G → ℝ) :
    (wilsonProfileRealizations h hG S Λ₀ hbase hn W rho).card =
      ∏ j, (latinonBallLatinFamily hn (W j) (rho j)).card :=
  (wilsonLatinBlockTemplate h hG).card_restrictedRealizations S Λ₀ hbase _

/-- Sharp local entropy count for the previous CDR paper's actual Wilson
construction. A completed base layout is explicit; no global enumeration of
all CDR systems, arbitrary AAC prescription, or new completion theorem is asserted. -/
theorem wilson_distinguished_latinon_blocks_entropy_count {g : ℕ}
    (G : Finset (Finset (Fin g))) (hG : STS.IsSTS G)
    (W : Ix G → LatinonMeasure) (hfinite : ∀ j, latinonRate (W j) ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : Ix G → ℝ, (∀ j, 0 < rho j ∧ rho j ≤ r) ∧
      ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∀ (a b c : ℕ) (h : WCond a b c g n)
        (S : CDRBicolour.STS (Fin (a+b+c)))
        (_hS : CDRBicolour.IsStrictBicolouring S (col3 a b c))
        (Λ₀ : Ix G → LatinArray n) (hbase : crossP h Λ₀ ⊆ S.blocks),
      (Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal-eta)) ≤
        ((wilsonProfileRealizations h hG S Λ₀ hbase (hN.trans_le hn) W rho).card : ℝ) ∧
      ((wilsonProfileRealizations h hG S Λ₀ hbase (hN.trans_le hn) W rho).card : ℝ) ≤
        Real.exp (∑ j, (n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate (W j)).toReal+eta))) ∧
      ∀ B ∈ wilsonProfileRealizations h hG S Λ₀ hbase (hN.trans_le hn) W rho,
        ∃ S' : CDRBicolour.STS (Fin (a+b+c)), S'.blocks = B ∧
          CDRBicolour.IsStrictBicolouring S' (col3 a b c) := by
  obtain ⟨rho,hrho,N,hN,hcount⟩ :=
    cdr_distinguished_latinon_blocks_entropy_count W hfinite r eta hr heta
  refine ⟨rho,hrho,N,hN,?_⟩
  intro n hn a b c h S hS Λ₀ hbase
  exact hcount n hn (col3 a b c) (wilsonLatinBlockTemplate h hG) S hS Λ₀ hbase

end LatinonEntropy

#check LatinonEntropy.finite_rate_factorization_entropy_count
#check LatinonEntropy.finite_rate_factorization_pattern_log_count
#print axioms LatinonEntropy.card_wilsonProfileRealizations
#print axioms LatinonEntropy.wilson_distinguished_latinon_blocks_entropy_count
