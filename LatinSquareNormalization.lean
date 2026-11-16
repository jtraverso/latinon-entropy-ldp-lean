module

public import LatinBlockCounting
public import LatinDensityLowerBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Every probability table has nonpositive entropy relative to its
normalized positive block volumes, including zero masses. -/
theorem latin_coarse_entropy_nonpos {n r s q : ℕ} (hn : 0 < n)
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (hw : ∀ L ∈ S, 0 ≤ w L) (htotal : ∑ L ∈ S, w L = 1)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    latinLawCoarseEntropy S w row col sym ≤ 0 := by
  have ht := latin_law_block_table_total hn S w htotal row col sym
  have hv := latin_block_volume_total hn row col sym
  have hpoint : ∀ b ∈ latinActiveBlocks row col sym,
      latinLawBlockTable S w row col sym b*
          Real.log (latinBlockVolume row col sym b/latinLawBlockTable S w row col sym b) ≤
        latinBlockVolume row col sym b-latinLawBlockTable S w row col sym b := by
    intro b hb
    have hm := latin_law_block_table_nonneg S w hw row col sym b
    have hvol := latinBlockVolume_pos hn row col sym b hb
    by_cases hz : latinLawBlockTable S w row col sym b = 0
    · simpa only [hz,zero_mul,sub_zero] using hvol.le
    · have hmp : 0 < latinLawBlockTable S w row col sym b := lt_of_le_of_ne hm (Ne.symm hz)
      have hlog := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hvol hmp)) hm
      have he : latinLawBlockTable S w row col sym b*
          (latinBlockVolume row col sym b/latinLawBlockTable S w row col sym b-1) =
          latinBlockVolume row col sym b-latinLawBlockTable S w row col sym b := by
        rw [mul_sub,mul_div_cancel₀ _ hz,mul_one]
      rwa [he] at hlog
  have hsum := sum_le_sum hpoint
  rw [sum_sub_distrib,hv,ht,sub_self] at hsum
  exact hsum

/-- Uniform global upper normalization, also valid for empty subfamilies. -/
theorem exists_total_latin_count_upper (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ S : Finset (LatinArray n),
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+eta)) := by
  obtain ⟨M,hM,hcount⟩ := exists_latin_block_count_exp_threshold eta heta
  refine ⟨M^2+1,by omega,?_⟩
  intro n hn S
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < M^2+1) hn
  let color : Fin n → Fin 1 := fun _ => 0
  have hsize : ∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber color a).card : ℝ) := by
    intro a
    have hreal : (M : ℝ)^2 ≤ (n : ℝ) := by exact_mod_cast (show M^2 ≤ n by omega)
    simpa [color,symbolColorFiber] using hreal
  by_cases hS : S.Nonempty
  · have hcard : (S.card : ℝ) ≠ 0 := (Nat.cast_pos.mpr (card_pos.mpr hS)).ne'
    have htotal : (∑ L ∈ S, (1 : ℝ)/(S.card : ℝ)) = 1 := by simp [hcard]
    have hE := latin_coarse_entropy_nonpos hnpos S (fun _ => 1/(S.card : ℝ))
      (fun L _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) htotal color color color
    apply (hcount n 1 1 1 color color color S hnpos hsize).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [hE]) (sq_nonneg (n : ℝ))
  · have hz : S.card = 0 := Nat.eq_zero_of_not_pos (fun h => hS (card_pos.mp h))
    rw [hz,Nat.cast_zero]
    exact (Real.exp_pos _).le

local instance (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

def allLatinSquares (n : ℕ) : Finset (LatinArray n) := univ

/-- The actual total number has the normalization required for an LDP at
speed n^2, with the second-order constant -2 and every eta>0. -/
theorem total_latin_square_count_normalization (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-eta)) ≤ (allLatinSquares n).card ∧
      ((allLatinSquares n).card : ℝ) ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+eta)) := by
  obtain ⟨NU,hNU,hupper⟩ := exists_total_latin_count_upper eta heta
  obtain ⟨NL,hNL,hlower⟩ := finite_latin_density_lower_bound 1 1 1 eta
    (by norm_num) (by norm_num) heta
  refine ⟨max NU NL,hNU.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnU : NU ≤ n := (le_max_left _ _).trans hn
  have hnL : NL ≤ n := (le_max_right _ _).trans hn
  have hline : (∑ _ : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  have hl := (hlower n hnL (fun _ _ _ => 1) (fun _ _ _ => ⟨le_rfl,le_rfl⟩)
    (fun _ _ => hline) (fun _ _ => hline) (fun _ _ => hline)).2
  have hzero : latinGridDensityEntropy (fun (_ _ _ : Fin n) => (1 : ℝ)) = 0 := by
    simp [latinGridDensityEntropy]
  rw [hzero,add_zero] at hl
  refine ⟨hl.trans (Nat.cast_le.mpr (card_le_card (subset_univ _))),hupper n hnU _⟩

end LatinonEntropy

#print axioms LatinonEntropy.latin_coarse_entropy_nonpos
#print axioms LatinonEntropy.exists_total_latin_count_upper
#print axioms LatinonEntropy.total_latin_square_count_normalization
