module

public import ProfileCutNoise
public import ProfileCutPropagation
public import PermanentCoordinateValues
public import HistoryLocality

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem killed_noise_matrix_pairing {n : ℕ} (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (g : LatinHistory n → Fin n → Fin n → ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) :
    matrixPairing (killedRowNoise Good (fun a => permanentMarginal (S.matrix a)) h sigma) (g h) =
      killedPermanentalStatistic S Good g h sigma := by
  by_cases hlive : historyLive Good h
  · simp only [matrixPairing,killedRowNoise,killedPermanentalStatistic,hlive,ite_true,
      sub_mul,sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    exact rowPermutationMatrix_row_value sigma i (g h i)
  · simp only [matrixPairing,killedRowNoise,killedPermanentalStatistic,hlive,ite_false,
      zero_mul,sum_const_zero]

theorem matrixPairing_cut_mask {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → Fin n → ℝ) (U V : Finset (Fin n)) :
    matrixPairing B (fun i j => if i ∈ U ∧ j ∈ V then w i j else 0) =
      ∑ i ∈ U, ∑ j ∈ V, B i j*w i j := by
  simp [matrixPairing,ite_and,mul_ite]

theorem profile_cut_noise_value {n : ℕ} (P : PositiveLatinProfile n)
    (t : ℕ) (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (ht : h.length < t) :
    killedPermanentalStatistic S Good (profileCutTest P t U V) h sigma =
      profileCutNoiseIncrement P t S Good U V h sigma := by
  rw [← killed_noise_matrix_pairing]
  have he : profileCutTest P t U V h = (fun i j => if i ∈ U ∧ j ∈ V then
      propagationKernel (fun s => profileHazard P s i j) h.length t else 0) := by
    funext i j
    simp only [profileCutTest,ht,true_and]
  rw [he,matrixPairing_cut_mask]
  unfold profileCutNoiseIncrement
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem profile_cut_noise_zero_after {n : ℕ} (P : PositiveLatinProfile n)
    (t : ℕ) (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (ht : t ≤ h.length) (sigma : Equiv.Perm (Fin n)) :
    killedPermanentalStatistic S Good (profileCutTest P t U V) h sigma = 0 := by
  simp [killedPermanentalStatistic,profileCutTest,not_lt.mpr ht,permutationStatistic,matrixPairing]

theorem profile_cut_noise_prefix_identity {n : ℕ} (P : PositiveLatinProfile n)
    (t : ℕ) (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (ht : t ≤ h.length) :
    pathSum (killedPermanentalStatistic S Good (profileCutTest P t U V)) h =
      pathSum (profileCutNoiseIncrement P t S Good U V) (historyPrefix h t) := by
  rw [pathSum_local_to_prefix _ t (fun g hg sigma => profile_cut_noise_zero_after P t S Good U V g hg sigma) h ht]
  exact pathSum_congr_before _ _ t (fun g hg sigma => profile_cut_noise_value P t S Good U V g sigma hg)
    (historyPrefix h t) (historyPrefix_length h t ht).le

end LatinonEntropy

#print axioms LatinonEntropy.profile_cut_noise_prefix_identity
