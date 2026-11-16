module

public import ProfileProcess
public import HistoryAbsoluteBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileCutTest {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ)
    (S T : Finset (Fin n)) (h : LatinHistory n) (i j : Fin n) : ℝ :=
  if h.length < t ∧ i ∈ S ∧ j ∈ T then
    propagationKernel (fun s => profileHazard P s i j) h.length t else 0

theorem profileCutTest_bounds {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ)
    (S T : Finset (Fin n)) (h : LatinHistory n) (i j : Fin n) :
    0 ≤ profileCutTest P t S T h i j ∧ |profileCutTest P t S T h i j| ≤ 1 := by
  unfold profileCutTest
  split_ifs
  · have hb := propagationKernel_bounds (fun s => profileHazard P s i j)
      (fun s => P.hazard_mem_unit s i j) h.length t
    exact ⟨hb.1,by simpa only [abs_of_nonneg hb.1] using hb.2⟩
  · simp

theorem profile_cut_noise_full_tail {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (t : ℕ) (S T : Finset (Fin n)) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u ≤ (n : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
          (profileProcessGood P eps heps budget) (profileCutTest P t S T)) h|
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ))))) :=
  latinStoppedProcess_deviation_le P.npos (profileCorrectionParameters P eps heps)
    (profileCandidate P) budget m hm hsize (profileCutTest P t S T)
    (fun h i j => (profileCutTest_bounds P t S T h i j).2) n P.npos u hu0 hu

/-- Union bound on one fixed history law. The drift exception must be
charged separately, once, rather than once for every cut. -/
theorem finite_history_union_bound {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] (K : FiniteKernel Ω) (N : ℕ) (E : I → List Ω → Prop)
    (b : ℝ) (hb : ∀ i, (∑ h ∈ histories Ω N,
      if E i h then historyWeight K h else 0) ≤ b) :
    (∑ h ∈ histories Ω N, if ∃ i, E i h then historyWeight K h else 0) ≤
      (Fintype.card I : ℝ)*b := by
  calc
    _ ≤ ∑ h ∈ histories Ω N, ∑ i, if E i h then historyWeight K h else 0 := by
      apply sum_le_sum
      intro h _
      by_cases he : ∃ i, E i h
      · simp only [he,ite_true]
        obtain ⟨i,hi⟩ := he
        have hs := single_le_sum (s := (univ : Finset I))
          (f := fun j => if E j h then historyWeight K h else 0)
          (fun j _ => by split_ifs; exact historyWeight_nonneg K h; exact le_rfl) (mem_univ i)
        simpa only [hi,ite_true] using hs
      · simp only [he,ite_false]
        exact sum_nonneg (fun i _ => by split_ifs; exact historyWeight_nonneg K h; exact le_rfl)
    _ = ∑ i, ∑ h ∈ histories Ω N, if E i h then historyWeight K h else 0 := sum_comm
    _ ≤ ∑ _i : I, b := sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

theorem profile_simultaneous_cut_noise {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (Nmain : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (n : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if ∃ t : Fin Nmain, ∃ S T : Finset (Fin n),
        u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
          (profileProcessGood P eps heps budget) (profileCutTest P t.val S T)) h|
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      ((Nmain : ℝ)*((2 : ℝ)^n)^2)*
        (2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
  let E : (Fin Nmain × Finset (Fin n) × Finset (Fin n)) → LatinHistory n → Prop :=
    fun v h => u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) (profileCutTest P v.1.val v.2.1 v.2.2)) h|
  have he : ∀ h, (∃ t : Fin Nmain, ∃ S T : Finset (Fin n),
      u ≤ |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
        (profileProcessGood P eps heps budget) (profileCutTest P t.val S T)) h|) ↔ ∃ v, E v h := by
    intro h
    constructor
    · rintro ⟨t,S,T,ht⟩; exact ⟨⟨t,S,T⟩,ht⟩
    · rintro ⟨⟨t,S,T⟩,ht⟩; exact ⟨t,S,T,ht⟩
  simp_rw [he]
  have hc : (Fintype.card (Fin Nmain × Finset (Fin n) × Finset (Fin n)) : ℝ) =
      (Nmain : ℝ)*((2 : ℝ)^n)^2 := by
    simp [Fintype.card_prod,Fintype.card_finset,pow_two]
  rw [← hc]
  apply finite_history_union_bound
  intro v
  exact profile_cut_noise_full_tail P eps heps budget m hm hsize v.1.val v.2.1 v.2.2 u hu0 hu

end LatinonEntropy

#print axioms LatinonEntropy.profile_simultaneous_cut_noise
