module

public import HistoryEntropyCount
public import HistoryCardinality
public import ProfileTotalEntropy
public import UniformProfileCloseness

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileLatinHistoryAtoms {n : ℕ} (P : PositiveLatinProfile n) (eta : ℝ) :=
  goodHistoryAtoms (Ω := Equiv.Perm (Fin n)) n
    (fun h => LatinHistoryValid h ∧ profileCutClose P h eta)

theorem profile_latin_bad_mass_le_approximation {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (eta : ℝ) :
    historyEventMass ((profileProcessPolicy P eps heps budget).kernel P.npos) n
      (fun h => ¬(LatinHistoryValid h ∧ profileCutClose P h eta)) ≤
      historyEventMass ((profileProcessPolicy P eps heps budget).kernel P.npos) n
        (profileApproximationBad P eps heps budget T eta) := by
  let S := profileProcessPolicy P eps heps budget
  let K := S.kernel P.npos
  have hi : ∀ h ∈ histories (Equiv.Perm (Fin n)) n, 0 < historyWeight K h →
      ¬(LatinHistoryValid h ∧ profileCutClose P h eta) →
        profileApproximationBad P eps heps budget T eta h ∨ False := by
    intro h hh hp hbad
    have hv := S.positive_history_valid P.npos n le_rfl h hh hp
    exact Or.inl (Or.inr (fun hc => hbad ⟨hv,hc⟩))
  have h := history_event_mass_split K n
    (fun h => ¬(LatinHistoryValid h ∧ profileCutClose P h eta))
    (profileApproximationBad P eps heps budget T eta) (fun _ => False) hi
  have hz : historyEventMass K n (fun _ => False) = 0 := by simp [historyEventMass]
  simpa only [hz,add_zero] using h

theorem profile_latin_bad_mass_le_rate {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (hTwo : 2 ≤ eps*(n : ℝ)) :
    historyEventMass
      ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) n
      (fun h => ¬(LatinHistoryValid h ∧ profileCutClose P h (4*eps))) ≤
      profileClosenessRate a b eps m n := by
  let v := fixedCutDensity a b eps*(n : ℝ)^2/4
  have h1 := profile_latin_bad_mass_le_approximation P eps heps v (mainRange eps n) (4*eps)
  have hth := main_range_full_error_le_four_eps a b eps (ha ▸ P.a_pos) heps heps1 n hTwo
  have h2 := profile_approximation_bad_mass_le_full P eps heps v (mainRange eps n)
    (eps*(n : ℝ)^2/8) (4*eps) hth ((profileProcessPolicy P eps heps v).kernel P.npos)
  have h3 := profile_full_bad_rate_bound P a b eps heps heps1 ha hb m hm hsize
    (mainRange eps n) (mainRange_degree eps heps1 n)
  exact h1.trans (h2.trans h3)

/-- A finite lower bound for distinct valid full row histories near the
actual prescribed tensor. The exceptional event is charged in cardinality. -/
theorem profile_finite_latin_history_count {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (hTwo : 2 ≤ eps*(n : ℝ))
    (hsmall : profileClosenessRate a b eps m n < 1) :
    profileEntropy P-2*(n : ℝ)^2-(n : ℝ)*profileRowEntropyError P a b eps heps m-
      (n : ℝ)*Real.log (n : ℝ)-
      profileClosenessRate a b eps m n*((n : ℝ)^2*Real.log (n : ℝ))-Real.log 2 ≤
        Real.log ((profileLatinHistoryAtoms P (4*eps)).card : ℝ) := by
  let v := fixedCutDensity a b eps*(n : ℝ)^2/4
  let K := (profileProcessPolicy P eps heps v).kernel P.npos
  let Good := fun h => LatinHistoryValid h ∧ profileCutClose P h (4*eps)
  let L := (n : ℝ)^2*Real.log (n : ℝ)
  have hbad := profile_latin_bad_mass_le_rate P a b eps heps heps1 ha hb m hm hsize hTwo
  have hcount := history_entropy_to_good_count K n Good L (hbad.trans_lt hsmall)
    (latin_history_card_reference_cap n P.npos)
  have hent := profile_history_entropy_lower P a b eps heps heps1 ha hb m hm hsize
  have hcost := mul_le_mul_of_nonneg_right hbad
    (mul_nonneg (sq_nonneg (n : ℝ)) (Real.log_natCast_nonneg n))
  dsimp only [K,Good,L,v] at hcount
  change _ ≤ Real.log ((profileLatinHistoryAtoms P (4*eps)).card : ℝ) at hcount
  linarith only [hcount,hent,hcost]

end LatinonEntropy

#print axioms LatinonEntropy.profile_latin_bad_mass_le_rate
#print axioms LatinonEntropy.profile_finite_latin_history_count
