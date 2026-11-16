module

public import WeightedJensen

@[expose] public section

/-! Explicit finite histories, stored with the newest outcome first. No
conditional-expectation or stochastic-process theorem is assumed. -/

noncomputable section

namespace LatinonEntropy

open Finset

structure FiniteKernel (Ω : Type*) [Fintype Ω] where
  transition : List Ω → Ω → ℝ
  nonneg : ∀ h a, 0 ≤ transition h a
  total : ∀ h, ∑ a, transition h a = 1

def histories (Ω : Type*) [Fintype Ω] [DecidableEq Ω] : ℕ → Finset (List Ω)
  | 0 => {[]}
  | t+1 => (histories Ω t).biUnion (fun h => univ.image (fun a => a::h))

theorem histories_cons {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {t : ℕ} {h : List Ω} (hh : h ∈ histories Ω t) (a : Ω) :
    a::h ∈ histories Ω (t+1) := by
  exact mem_biUnion.mpr ⟨h,hh,mem_image.mpr ⟨a,mem_univ _,rfl⟩⟩

theorem histories_length {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {t : ℕ} {h : List Ω} (hh : h ∈ histories Ω t) : h.length = t := by
  induction t generalizing h with
  | zero =>
    have he : h = [] := by simpa only [histories,mem_singleton] using hh
    simp [he]
  | succ t ih =>
    obtain ⟨g,hg,hm⟩ := mem_biUnion.mp hh
    obtain ⟨a,_,rfl⟩ := mem_image.mp hm
    simpa using congrArg Nat.succ (ih hg)

theorem history_sum_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (t : ℕ) (F : List Ω → ℝ) :
    (∑ h ∈ histories Ω (t+1), F h) = ∑ h ∈ histories Ω t, ∑ a, F (a::h) := by
  classical
  have hd : ∀ h ∈ histories Ω t, ∀ g ∈ histories Ω t, h ≠ g →
      Disjoint (univ.image (fun a : Ω => a::h)) (univ.image (fun a : Ω => a::g)) := by
    intro h _ g _ hne
    apply disjoint_left.mpr
    intro l hl hl'
    obtain ⟨a,_,ha⟩ := mem_image.mp hl
    obtain ⟨b,_,hb⟩ := mem_image.mp hl'
    exact hne (by simpa using congrArg List.tail (ha.trans hb.symm))
  rw [histories,Finset.sum_biUnion hd]
  apply sum_congr rfl
  intro h _
  rw [Finset.sum_image]
  intro a _ b _ he
  exact (List.cons.inj he).1

def historyWeight {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω) : List Ω → ℝ
  | [] => 1
  | a::h => historyWeight K h * K.transition h a

theorem historyWeight_nonneg {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω)
    (h : List Ω) : 0 ≤ historyWeight K h := by
  induction h with
  | nil => exact zero_le_one
  | cons a h ih => exact mul_nonneg ih (K.nonneg h a)

theorem historyWeight_total {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) : (∑ h ∈ histories Ω t, historyWeight K h) = 1 := by
  induction t with
  | zero => simp [histories,historyWeight]
  | succ t ih =>
    rw [history_sum_succ]
    simp only [historyWeight,← mul_sum,K.total,mul_one]
    exact ih

def historyExpectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (F : List Ω → ℝ) : ℝ :=
  ∑ h ∈ histories Ω t, historyWeight K h * F h

theorem historyExpectation_tower {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (F : List Ω → ℝ) :
    historyExpectation K (t+1) F =
      historyExpectation K t (fun h => ∑ a, K.transition h a * F (a::h)) := by
  unfold historyExpectation
  rw [history_sum_succ]
  apply sum_congr rfl
  intro h _
  simp only [historyWeight,mul_sum,mul_assoc]

theorem historyExpectation_const {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (c : ℝ) :
    historyExpectation K t (fun _ => c) = c := by
  rw [historyExpectation,← sum_mul,historyWeight_total,one_mul]

theorem historyExpectation_mono {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) {F G : List Ω → ℝ}
    (h : ∀ g ∈ histories Ω t, F g ≤ G g) :
    historyExpectation K t F ≤ historyExpectation K t G :=
  sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (h g hg) (historyWeight_nonneg K g))

theorem historyExpectation_add {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (F G : List Ω → ℝ) :
    historyExpectation K t (fun h => F h+G h) =
      historyExpectation K t F+historyExpectation K t G := by
  simp only [historyExpectation,mul_add,sum_add_distrib]

theorem historyExpectation_mul {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (c : ℝ) (F : List Ω → ℝ) :
    historyExpectation K t (fun h => c*F h) = c*historyExpectation K t F := by
  unfold historyExpectation
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  ring

end LatinonEntropy

#print axioms LatinonEntropy.historyWeight_total
#print axioms LatinonEntropy.historyExpectation_tower
