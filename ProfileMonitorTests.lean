module

public import ProfileObservationMonitor
public import ProfileCutNoiseValue
public import ProfileSurvivalProbability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def timeCutWeight {n : ℕ} (I : Finset (Fin n)) (t : ℕ) : ℝ :=
  if t ∈ I.image Fin.val then 1 else 0

theorem timeCutWeight_abs_le {n : ℕ} (I : Finset (Fin n)) (t : ℕ) : |timeCutWeight I t| ≤ 1 := by
  unfold timeCutWeight
  split_ifs <;> norm_num

theorem timeCutWeight_at_fin {n : ℕ} (I : Finset (Fin n)) (x : Fin n) :
    timeCutWeight I x.val = if x ∈ I then 1 else 0 := by
  have he : x.val ∈ I.image Fin.val ↔ x ∈ I := by
    constructor
    · intro hx
      obtain ⟨y,hy,he⟩ := mem_image.mp hx
      exact (Fin.ext he) ▸ hy
    · intro hx; exact mem_image.mpr ⟨x,hx,rfl⟩
  simp only [timeCutWeight,he]

def profileMonitorWeight {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (I : Finset (Fin n)) (t : ℕ) (i j : Fin n) : ℝ :=
  hazardMonitor (fun s => profileHazard P s i j) (timeCutWeight I) t T

theorem profileMonitorWeight_abs_le {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (I : Finset (Fin n)) (t : ℕ) (i j : Fin n) : |profileMonitorWeight P T I t i j| ≤ 2 :=
  hazardMonitor_abs_le_two _ _ (fun s => P.hazard_mem_unit s i j) (timeCutWeight_abs_le I) t T

def profileMonitorTest {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (I U V : Finset (Fin n)) (h : LatinHistory n) (i j : Fin n) : ℝ :=
  if h.length < T ∧ i ∈ U ∧ j ∈ V then profileMonitorWeight P T I h.length i j/2 else 0

theorem profileMonitorTest_abs_le {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (I U V : Finset (Fin n)) (h : LatinHistory n) (i j : Fin n) : |profileMonitorTest P T I U V h i j| ≤ 1 := by
  unfold profileMonitorTest
  split_ifs
  · rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
      simpa only [one_mul] using profileMonitorWeight_abs_le P T I h.length i j)
  · norm_num

theorem profile_monitor_noise_full_tail {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (T : ℕ) (I U V : Finset (Fin n)) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (n : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
          (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h|
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ))))) :=
  latinStoppedProcess_deviation_le P.npos (profileCorrectionParameters P eps heps)
    (profileCandidate P) budget m hm hsize (profileMonitorTest P T I U V)
    (profileMonitorTest_abs_le P T I U V) n P.npos u hu0 hu

theorem profile_simultaneous_monitor_noise {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (T : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (n : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if ∃ I U V : Finset (Fin n),
        u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
          (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h|
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      (8 : ℝ)^n*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
  let E : (Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) → LatinHistory n → Prop :=
    fun v h => u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) (profileMonitorTest P T v.1 v.2.1 v.2.2)) h|
  have he : ∀ h, (∃ I U V : Finset (Fin n),
      u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
        (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h|) ↔ ∃ v, E v h := by
    intro h
    constructor
    · rintro ⟨I,U,V,ht⟩; exact ⟨⟨I,U,V⟩,ht⟩
    · rintro ⟨⟨I,U,V⟩,ht⟩; exact ⟨I,U,V,ht⟩
  simp_rw [he]
  have hc : (Fintype.card (Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) : ℝ) = (8 : ℝ)^n := by
    simp only [Fintype.card_prod,Fintype.card_finset,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [← mul_pow,← mul_pow]
    norm_num
  rw [← hc]
  apply finite_history_union_bound
  intro v
  exact profile_monitor_noise_full_tail P eps heps budget m hm hsize T v.1 v.2.1 v.2.2 u hu0 hu

end LatinonEntropy

#print axioms LatinonEntropy.profile_simultaneous_monitor_noise
