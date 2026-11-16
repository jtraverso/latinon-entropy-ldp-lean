module

public import FallbackEntropy
public import FluidRowUpper
public import HistoryExpectationTools

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem expected_tail_row_entropy_lower {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (t : ℕ)
    (ht : t < n) (hmain : mainRange eps n < t) :
    profileFluidRowEntropy P t-(n : ℝ) ≤
      historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) t
        (kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos)) := by
  let S := profileProcessPolicy P eps heps budget
  let K := S.kernel P.npos
  have hup := profile_fluid_row_upper P ⟨t,ht⟩
  calc
    _ ≤ (n : ℝ)*Real.log ((n : ℝ)-t)-(n : ℝ) := sub_le_sub_right hup _
    _ = historyExpectation K t (fun _ => (n : ℝ)*Real.log ((n : ℝ)-t)-(n : ℝ)) :=
      (historyExpectation_const K t _).symm
    _ ≤ _ := by
      apply historyExpectation_mono_positive
      intro h hh hp
      have hlen := histories_length hh
      have hv := S.positive_history_valid P.npos t ht.le h hh hp
      have hrow := profile_tail_kernel_entropy_lower P eps heps budget h hv
        (by rw [hlen]; exact ht) (by rw [hlen]; exact hmain)
      simpa only [hlen] using hrow

theorem expected_boundary_row_entropy_lower {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (t : ℕ) (ht : t < n) :
    profileFluidRowEntropy P t-(n : ℝ)*Real.log (n : ℝ) ≤
      historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) t
        (kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos)) := by
  have hup := profile_fluid_row_upper_log_n P ⟨t,ht⟩
  have hnonneg := historyExpectation_nonneg ((profileProcessPolicy P eps heps budget).kernel P.npos) t
    (kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos))
    (fun h _ => kernelEntropy_nonneg _ h)
  exact (sub_nonpos.mpr hup).trans hnonneg

end LatinonEntropy

#print axioms LatinonEntropy.expected_tail_row_entropy_lower
#print axioms LatinonEntropy.expected_boundary_row_entropy_lower
