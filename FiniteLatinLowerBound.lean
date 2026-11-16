module

public import ProfileLatinArrayCount
public import HistoryGoodExistence

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology
open scoped Classical

theorem profileCutClose_mono {n : ℕ} (P : PositiveLatinProfile n) (h : LatinHistory n)
    {eta rho : ℝ} (her : eta ≤ rho) (hc : profileCutClose P h eta) : profileCutClose P h rho := by
  intro I U V
  exact (hc I U V).trans (mul_le_mul_of_nonneg_right her (sq_nonneg (n : ℝ)))

theorem profile_latin_array_card_mono {n : ℕ} (P : PositiveLatinProfile n)
    {eta rho : ℝ} (her : eta ≤ rho) :
    (profileLatinArrayFamily P eta).card ≤ (profileLatinArrayFamily P rho).card := by
  rw [profile_latin_array_family_card,profile_latin_array_family_card]
  apply card_le_card
  intro h hh
  simp only [profileLatinHistoryAtoms,goodHistoryAtoms,mem_filter,mem_univ,true_and] at hh ⊢
  exact ⟨hh.1,profileCutClose_mono P h.val her hh.2⟩

theorem log_natCast_mono {u v : ℕ} (huv : u ≤ v) :
    Real.log (u : ℝ) ≤ Real.log (v : ℝ) := by
  by_cases hu : u = 0
  · simpa only [hu,Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg v
  · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hu)) (Nat.cast_le.mpr huv)

theorem eventually_uniform_profile_family_nonempty (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      (profileLatinArrayFamily P (4*eps)).Nonempty := by
  obtain ⟨m,hm⟩ := fixed_permanent_cap_index_exists a b eps
  have hprob := (tendsto_order.mp (profile_closeness_rate_tendsto_zero a b eps ha heps m)).2 1 (by norm_num)
  filter_upwards [hprob,eventually_permanentCapError_le_half m,
    eventually_ge_atTop ⌈(2 : ℝ)/eps⌉₊] with n hp hsize hnceil
  intro P hPa hPb
  have hdiv : (2 : ℝ)/eps ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hnceil)
  have hTwo : 2 ≤ eps*(n : ℝ) := by nlinarith only [(div_le_iff₀ heps).mp hdiv]
  have hbad := (profile_latin_bad_mass_le_rate P a b eps heps heps1 hPa hPb m hm hsize hTwo).trans_lt hp
  have hgood := goodHistoryAtoms_nonempty_of_bad_mass_lt_one
    ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) n
    (fun h => LatinHistoryValid h ∧ profileCutClose P h (4*eps)) hbad
  apply card_pos.mp
  rw [profile_latin_array_family_card]
  exact card_pos.mpr hgood

/-- For every positive cut tolerance and entropy loss, one size threshold
works for all profiles with fixed positive lower and finite upper bounds.
The family consists of distinct actual Latin arrays, with proved witnesses
for every prescribed cut. Nonemptiness is explicit, including zero-atom issues. -/
theorem eventually_uniform_finite_latin_lower_bound (a b rho eta : ℝ) (ha : 0 < a)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      (profileLatinArrayFamily P rho).Nonempty ∧
      Real.exp (profileEntropy P-(2+eta)*(n : ℝ)^2) ≤ (profileLatinArrayFamily P rho).card := by
  let eps := min 1 (rho/4)
  have heps : 0 < eps := lt_min (by norm_num) (div_pos hrho (by norm_num))
  have heps1 : eps ≤ 1 := min_le_left _ _
  have htol : 4*eps ≤ rho := by
    have h := min_le_right (1 : ℝ) (rho/4)
    change eps ≤ rho/4 at h
    linarith only [h]
  filter_upwards [eventually_uniform_profile_latin_array_count a b eps ha heps heps1 eta heta,
    eventually_uniform_profile_family_nonempty a b eps ha heps heps1] with n hcount hnonempty
  intro P hPa hPb
  have hc := hcount P hPa hPb
  have hcard := profile_latin_array_card_mono P htol
  have hnsmall := hnonempty P hPa hPb
  have hnlarge : (profileLatinArrayFamily P rho).Nonempty :=
    card_pos.mp ((card_pos.mpr hnsmall).trans_le hcard)
  refine ⟨hnlarge,?_⟩
  have hlog := log_natCast_mono hcard
  have hlower : profileEntropy P-(2+eta)*(n : ℝ)^2 ≤
      Real.log ((profileLatinArrayFamily P rho).card : ℝ) := by nlinarith only [hc,hlog]
  have hpos : (0 : ℝ) < (profileLatinArrayFamily P rho).card := Nat.cast_pos.mpr (card_pos.mpr hnlarge)
  exact (Real.exp_le_exp.mpr hlower).trans_eq (Real.exp_log hpos)

end LatinonEntropy

#print axioms LatinonEntropy.eventually_uniform_profile_family_nonempty
#print axioms LatinonEntropy.eventually_uniform_finite_latin_lower_bound
