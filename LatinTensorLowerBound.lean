module

public import LatinArrayProfileCuts

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology
open scoped Classical

local instance (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

/-- All Latin squares satisfying the tensor cuts, independently of any process. -/
def latinTensorCutFamily {n : ℕ} (p : Fin n → Fin n → Fin n → ℝ) (rho : ℝ) :
    Finset (LatinArray n) :=
  univ.filter (fun L => ∀ I U V : Finset (Fin n),
    |∑ x ∈ I, ∑ i ∈ U, ∑ j ∈ V, ((if L.val x i = j then (1 : ℝ) else 0)-p x i j)| ≤
      rho*(n : ℝ)^2)

theorem mem_latinTensorCutFamily_iff {n : ℕ} (P : PositiveLatinProfile n)
    (rho : ℝ) (L : LatinArray n) :
    L ∈ latinTensorCutFamily P.p rho ↔ latinArrayProfileCutClose P L rho := by
  simp only [latinTensorCutFamily,mem_filter,mem_univ,true_and,
    latinArrayProfileCutClose,latinArrayProfileCut]

theorem profile_latin_array_family_subset_tensor_family {n : ℕ}
    (P : PositiveLatinProfile n) (rho : ℝ) :
    profileLatinArrayFamily P rho ⊆ latinTensorCutFamily P.p rho := by
  intro L hL
  obtain ⟨h,hlen,hv,he,hc⟩ := profile_latin_array_family_witness P rho L hL
  have ha : historyToLatinArray h hlen hv = L := Subtype.ext he
  have hclose := (profile_cut_close_iff_array_cut_close P h hlen hv rho).mp hc
  rw [ha] at hclose
  exact (mem_latinTensorCutFamily_iff P rho L).mpr hclose

theorem eventually_uniform_latin_tensor_lower_bound (a b rho eta : ℝ) (ha : 0 < a)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      (latinTensorCutFamily P.p rho).Nonempty ∧
      Real.exp (profileEntropy P-(2+eta)*(n : ℝ)^2) ≤ (latinTensorCutFamily P.p rho).card := by
  filter_upwards [eventually_uniform_finite_latin_lower_bound a b rho eta ha hrho heta]
    with n hn
  intro P hPa hPb
  obtain ⟨hne,hcount⟩ := hn P hPa hPb
  have hsub := profile_latin_array_family_subset_tensor_family P rho
  exact ⟨hne.mono hsub,hcount.trans (Nat.cast_le.mpr (card_le_card hsub))⟩

/-- A process-free statement: one positive threshold works for every tensor
with the prescribed bounds and all three unit margins. -/
theorem finite_latin_tensor_lower_bound (a b rho eta : ℝ) (ha : 0 < a)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ p : Fin n → Fin n → Fin n → ℝ,
      (∀ x i j, a/(n : ℝ) ≤ p x i j ∧ p x i j ≤ b/(n : ℝ)) →
      (∀ x i, ∑ j, p x i j = 1) →
      (∀ x j, ∑ i, p x i j = 1) →
      (∀ i j, ∑ x, p x i j = 1) →
      (latinTensorCutFamily p rho).Nonempty ∧
      Real.exp (-(∑ x, ∑ i, ∑ j, p x i j*Real.log (p x i j))-
        (2+eta)*(n : ℝ)^2) ≤ (latinTensorCutFamily p rho).card := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_uniform_latin_tensor_lower_bound a b rho eta ha hrho heta)
  refine ⟨max 1 N,lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _),?_⟩
  intro n hn p hbounds hrow hcol htime
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_left _ _).trans hn)
  let z : Fin n := ⟨0,hnpos⟩
  have hab : a ≤ b := (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hnpos)).mp
    ((hbounds z z z).1.trans (hbounds z z z).2)
  let P : PositiveLatinProfile n := {
    npos := hnpos, p := p, a := a, b := b, a_pos := ha, a_le_b := hab,
    bounds := hbounds, row_mass := hrow, col_mass := hcol, time_mass := htime
  }
  exact hN n ((le_max_right _ _).trans hn) P rfl rfl

end LatinonEntropy
