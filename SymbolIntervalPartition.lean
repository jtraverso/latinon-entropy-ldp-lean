module

public import SymbolIntervalClasses
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- An ordered partition of [0,1] into positive-length symbol intervals. -/
structure SymbolIntervalPartition (q : ℕ) where
  q_pos : 0 < q
  cut : Fin (q+1) → ℝ
  strict : StrictMono cut
  first : cut 0 = 0
  last : cut (Fin.last q) = 1

namespace SymbolIntervalPartition

variable {q : ℕ} (P : SymbolIntervalPartition q)

def left (k : Fin q) : ℝ := P.cut k.castSucc
def right (k : Fin q) : ℝ := P.cut k.succ

theorem left_nonneg (k : Fin q) : 0 ≤ P.left k := by
  calc 0 = P.cut 0 := P.first.symm
       _ ≤ P.cut k.castSucc := P.strict.monotone (Fin.zero_le _)

theorem left_lt_right (k : Fin q) : P.left k < P.right k := by
  apply P.strict
  change k.val < k.val+1
  omega

theorem right_le_one (k : Fin q) : P.right k ≤ 1 := by
  calc P.cut k.succ ≤ P.cut (Fin.last q) := P.strict.monotone (by
         change k.val+1 ≤ q
         have hk := k.isLt
         omega)
       _ = 1 := P.last

theorem exists_class (n : ℕ) (z : Fin n) :
    ∃ k : Fin q, z ∈ symbolIntervalClass n (P.left k) (P.right k) := by
  let m : Fin (q+1) → ℕ := fun i => symbolFloorCut n (P.cut i)
  have hm0 : m 0 = 0 := by simp only [m,P.first,symbolFloorCut_zero]
  have hml : m (Fin.last q) = n := by simp only [m,P.last,symbolFloorCut_one]
  let S : Finset (Fin q) := univ.filter (fun k => z.val < m k.succ)
  have hS : S.Nonempty := by
    let k : Fin q := ⟨q-1,by have hq := P.q_pos; omega⟩
    have hk : k.succ = Fin.last q := by
      apply Fin.ext
      change q-1+1 = q
      have hq := P.q_pos
      omega
    refine ⟨k,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    rw [hk,hml]
    exact z.isLt
  let k := S.min' hS
  have hupper : z.val < m k.succ := (mem_filter.mp (min'_mem S hS)).2
  have hlower : m k.castSucc ≤ z.val := by
    by_cases hk0 : k.val = 0
    · have hk : k.castSucc = (0 : Fin (q+1)) := Fin.ext hk0
      rw [hk,hm0]
      exact Nat.zero_le _
    · by_contra hno
      have hz : z.val < m k.castSucc := Nat.lt_of_not_ge hno
      let prev : Fin q := ⟨k.val-1,by have hk := k.isLt; omega⟩
      have hp : prev.succ = k.castSucc := by
        apply Fin.ext
        change k.val-1+1 = k.val
        omega
      have hprev : prev ∈ S := by
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        rw [hp]
        exact hz
      have hmin : k ≤ prev := min'_le S prev hprev
      have hv : k.val ≤ k.val-1 := hmin
      omega
  refine ⟨k,?_⟩
  simp only [symbolIntervalClass,mem_filter,mem_univ,true_and]
  exact ⟨hlower,hupper⟩

theorem class_unique (n : ℕ) (z : Fin n) (k l : Fin q)
    (hk : z ∈ symbolIntervalClass n (P.left k) (P.right k))
    (hl : z ∈ symbolIntervalClass n (P.left l) (P.right l)) : k = l := by
  simp only [symbolIntervalClass,mem_filter,mem_univ,true_and] at hk hl
  rcases lt_trichotomy k l with hlt | heq | hgt
  · have hsep : P.right k ≤ P.left l := P.strict.monotone (by
      change k.val+1 ≤ l.val
      exact Nat.succ_le_of_lt hlt)
    have hcut := symbolFloorCut_mono n hsep
    omega
  · exact heq
  · have hsep : P.right l ≤ P.left k := P.strict.monotone (by
      change l.val+1 ≤ k.val
      exact Nat.succ_le_of_lt hgt)
    have hcut := symbolFloorCut_mono n hsep
    omega

/-- The actual color map on whole grid symbols; no rounding hypothesis is assumed. -/
def color (n : ℕ) (z : Fin n) : Fin q := Classical.choose (P.exists_class n z)

theorem color_mem (n : ℕ) (z : Fin n) :
    z ∈ symbolIntervalClass n (P.left (P.color n z)) (P.right (P.color n z)) :=
  Classical.choose_spec (P.exists_class n z)

theorem color_eq_iff (n : ℕ) (z : Fin n) (k : Fin q) :
    P.color n z = k ↔ z ∈ symbolIntervalClass n (P.left k) (P.right k) := by
  constructor
  · intro he
    simpa only [he] using P.color_mem n z
  · intro hk
    exact P.class_unique n z (P.color n z) k (P.color_mem n z) hk

theorem color_fiber (n : ℕ) (k : Fin q) :
    univ.filter (fun z => P.color n z = k) = symbolIntervalClass n (P.left k) (P.right k) := by
  ext z
  simp only [mem_filter,mem_univ,true_and,P.color_eq_iff]

theorem color_class_proportion_error {n : ℕ} (hn : 0 < n) (k : Fin q) :
    |((univ.filter (fun z => P.color n z = k)).card : ℝ)/(n : ℝ)-(P.right k-P.left k)| <
      1/(n : ℝ) := by
  rw [P.color_fiber]
  exact symbolIntervalClass_proportion_error hn _ _ (P.left_nonneg k)
    (P.left_lt_right k).le (P.right_le_one k)

theorem exists_color_class_size_threshold (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ k : Fin q,
      (M : ℝ)^2 ≤ ((univ.filter (fun z => P.color n z = k)).card : ℝ) := by
  have he : ∀ k : Fin q, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (M : ℝ)^2 ≤ ((symbolIntervalClass n (P.left k) (P.right k)).card : ℝ) := by
    intro k
    exact exists_symbolIntervalClass_size_threshold _ _ (P.left_nonneg k)
      (P.left_lt_right k) (P.right_le_one k) M
  choose N hN hsize using he
  refine ⟨max 1 (∑ k, N k),by omega,?_⟩
  intro n hn k
  rw [P.color_fiber]
  apply hsize k n
  have hNk := single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (mem_univ k)
  exact hNk.trans ((le_max_right _ _).trans hn)

end SymbolIntervalPartition

end LatinonEntropy

#print axioms LatinonEntropy.SymbolIntervalPartition.exists_class
#print axioms LatinonEntropy.SymbolIntervalPartition.class_unique
#print axioms LatinonEntropy.SymbolIntervalPartition.color_eq_iff
#print axioms LatinonEntropy.SymbolIntervalPartition.color_class_proportion_error
#print axioms LatinonEntropy.SymbolIntervalPartition.exists_color_class_size_threshold
