module

public import ProfileFluid

@[expose] public section

noncomputable section

namespace LatinonEntropy

/-- A concrete profile for every positive order: the hypotheses are inhabited. -/
def uniformLatinProfile (n : ℕ) (hn : 0 < n) : PositiveLatinProfile n := by
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hm : (∑ _ : Fin n, (1 : ℝ)/(n : ℝ)) = 1 := by simp [hnR]
  exact {
    npos := hn, p := fun _ _ _ => 1/(n : ℝ), a := 1, b := 1,
    a_pos := by norm_num, a_le_b := le_rfl,
    bounds := fun _ _ _ => ⟨le_rfl,le_rfl⟩,
    row_mass := fun _ _ => hm, col_mass := fun _ _ => hm, time_mass := fun _ _ => hm
  }

theorem positive_latin_profile_exists (n : ℕ) (hn : 0 < n) :
    ∃ P : PositiveLatinProfile n, P.a = 1 ∧ P.b = 1 :=
  ⟨uniformLatinProfile n hn,rfl,rfl⟩

end LatinonEntropy

#print axioms LatinonEntropy.positive_latin_profile_exists
