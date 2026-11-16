module

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini

Weighted extension of the counting chain proof in
counting-steiner-triple-systems, 52fda83038df7442c576e17edffba591db703cb8,
RequestProject/LL/Chain.lean. The finite family now has arbitrary positive
weights and the coordinate reference measures need not be uniform.
-/
public import WeightedLogSum
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def revealFibre {A I B : Type*} [DecidableEq B] (S : Finset A) (coords : Finset I)
    (key : I → ℕ) (f : I → A → B) (i : I) (x : A) : Finset A :=
  S.filter (fun y => ∀ j ∈ coords, key j < key i → f j y = f j x)

def availableReference {A I B : Type*} [DecidableEq B]
    (S : Finset A) (coords : Finset I) (key : I → ℕ) (f : I → A → B)
    (r : I → B → ℝ) (i : I) (x : A) : ℝ :=
  ∑ v ∈ (revealFibre S coords key f i x).image (f i), r i v

def weightedFamilyEntropy {A : Type*} (S : Finset A) (w : A → ℝ) : ℝ :=
  (∑ x ∈ S, w x) * Real.log (∑ x ∈ S, w x) - ∑ x ∈ S, w x * Real.log (w x)

/-- Finite weighted revealing bound. It includes the reference probabilities
instead of replacing them by the cardinality of the available set. -/
theorem weighted_chain_bound {A I B : Type*} [DecidableEq A] [DecidableEq B]
    (key : I → ℕ) (f : I → A → B) (w : A → ℝ) (r : I → B → ℝ)
    (coords : Finset I) (S : Finset A)
    (hkey : Set.InjOn key coords)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, (∀ i ∈ coords, f i x = f i y) → x = y)
    (hS : S.Nonempty) (hw : ∀ x ∈ S, 0 < w x)
    (hr : ∀ i ∈ coords, ∀ x ∈ S, 0 < r i (f i x)) :
    weightedFamilyEntropy S w ≤
      ∑ x ∈ S, w x * ∑ i ∈ coords,
        (Real.log (availableReference S coords key f r i x) - Real.log (r i (f i x))) := by
  classical
  induction hsize : coords.card generalizing coords S with
  | zero =>
      have hc : coords = ∅ := card_eq_zero.mp hsize
      obtain ⟨x,hx⟩ := hS
      have hsingle : S = {x} := by
        ext y
        simp only [mem_singleton]
        constructor
        · intro hy
          exact hdet y hy x hx (by simp [hc])
        · intro hy
          simpa [hy] using hx
      simp [weightedFamilyEntropy,hc,hsingle]
  | succ m ih =>
      have hne : coords.Nonempty := by rw [← card_pos]; omega
      obtain ⟨i0,hi0,hmin⟩ := coords.exists_min_image key hne
      let J := coords.erase i0
      have hJ : J.card = m := by dsimp [J]; rw [card_erase_of_mem hi0]; omega
      have hkeyJ : Set.InjOn key J := hkey.mono (by simp [J,Set.subset_def]; tauto)
      have hlt : ∀ j ∈ J, key i0 < key j := by
        intro j hj
        have hj' := mem_of_mem_erase hj
        have hne := ne_of_mem_erase hj
        rcases (hmin j hj').lt_or_eq with h | h
        · exact h
        · exact absurd (hkey hj' hi0 h.symm) hne
      let P := S.image (f i0)
      let Sv : B → Finset A := fun v => S.filter (fun x => f i0 x = v)
      let Wv : B → ℝ := fun v => ∑ x ∈ Sv v, w x
      let W : ℝ := ∑ x ∈ S, w x
      let R : ℝ := ∑ v ∈ P, r i0 v
      have hSv : ∀ v ∈ P, (Sv v).Nonempty := by
        intro v hv
        obtain ⟨x,hx,hfx⟩ := mem_image.mp hv
        exact ⟨x,mem_filter.mpr ⟨hx,hfx⟩⟩
      have hWv : ∀ v ∈ P, 0 < Wv v := by
        intro v hv
        exact Finset.sum_pos (fun x hx => hw x (mem_filter.mp hx).1) (hSv v hv)
      have hrP : ∀ v ∈ P, 0 < r i0 v := by
        intro v hv
        obtain ⟨x,hx,hfx⟩ := mem_image.mp hv
        rw [← hfx]
        exact hr i0 hi0 x hx
      have hmass : W = ∑ v ∈ P, Wv v := sum_by_coordinate S (f i0) (fun _ x => w x)
      have hlog : (∑ x ∈ S, w x * Real.log (w x)) =
          ∑ v ∈ P, ∑ x ∈ Sv v, w x * Real.log (w x) :=
        sum_by_coordinate S (f i0) (fun _ x => w x * Real.log (w x))
      have href : (∑ x ∈ S, w x * Real.log (r i0 (f i0 x))) =
          ∑ v ∈ P, Wv v * Real.log (r i0 v) := by
        calc
          _ = ∑ v ∈ P, ∑ x ∈ Sv v, w x * Real.log (r i0 v) :=
            sum_by_coordinate S (f i0) (fun v x => w x * Real.log (r i0 v))
          _ = _ := by simp only [← Finset.sum_mul]; rfl
      have hterm0 : ∀ x ∈ S, availableReference S coords key f r i0 x = R := by
        intro x _
        have heq : revealFibre S coords key f i0 x = S := by
          apply Finset.filter_true_of_mem
          intro y _ j hj hbefore
          exact False.elim (not_lt_of_ge (hmin j hj) hbefore)
        unfold availableReference
        rw [heq]
      have hfibre : ∀ x ∈ S, ∀ i ∈ J,
          revealFibre S coords key f i x = revealFibre (Sv (f i0 x)) J key f i x := by
        intro x hx i hi
        ext y
        simp only [revealFibre,Sv,mem_filter]
        constructor
        · rintro ⟨hy,h⟩
          exact ⟨⟨hy,h i0 hi0 (hlt i hi)⟩,fun j hj => h j (mem_of_mem_erase hj)⟩
        · rintro ⟨⟨hy,h0⟩,h⟩
          refine ⟨hy,fun j hj hji => ?_⟩
          by_cases hji0 : j = i0
          · subst j; exact h0
          · exact h j (mem_erase.mpr ⟨hji0,hj⟩) hji
      have hsplit : ∀ x ∈ S,
          (∑ i ∈ coords, (Real.log (availableReference S coords key f r i x) - Real.log (r i (f i x)))) =
          (Real.log R - Real.log (r i0 (f i0 x))) +
            ∑ i ∈ J, (Real.log (availableReference (Sv (f i0 x)) J key f r i x) - Real.log (r i (f i x))) := by
        intro x hx
        rw [← add_sum_erase coords _ hi0,hterm0 x hx]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        unfold availableReference
        rw [hfibre x hx i hi]
      have hrec :
          (∑ x ∈ S, w x * ∑ i ∈ J,
            (Real.log (availableReference (Sv (f i0 x)) J key f r i x) - Real.log (r i (f i x)))) =
          ∑ v ∈ P, ∑ x ∈ Sv v, w x * ∑ i ∈ J,
            (Real.log (availableReference (Sv v) J key f r i x) - Real.log (r i (f i x))) :=
        sum_by_coordinate S (f i0) (fun v x => w x * ∑ i ∈ J,
          (Real.log (availableReference (Sv v) J key f r i x) - Real.log (r i (f i x))))
      have hroot :
          (∑ x ∈ S, w x * ∑ i ∈ coords,
            (Real.log (availableReference S coords key f r i x) - Real.log (r i (f i x)))) =
          W * Real.log R - (∑ v ∈ P, Wv v * Real.log (r i0 v)) +
            ∑ v ∈ P, ∑ x ∈ Sv v, w x * ∑ i ∈ J,
              (Real.log (availableReference (Sv v) J key f r i x) - Real.log (r i (f i x))) := by
        calc
          _ = ∑ x ∈ S, w x * ((Real.log R - Real.log (r i0 (f i0 x))) +
                ∑ i ∈ J, (Real.log (availableReference (Sv (f i0 x)) J key f r i x) -
                  Real.log (r i (f i x)))) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hsplit x hx]
          _ = _ := by
            simp_rw [mul_add,mul_sub]
            rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,href,hrec]
      have hchild : ∀ v ∈ P, weightedFamilyEntropy (Sv v) w ≤
          ∑ x ∈ Sv v, w x * ∑ i ∈ J,
            (Real.log (availableReference (Sv v) J key f r i x) - Real.log (r i (f i x))) := by
        intro v hv
        apply ih J (Sv v) hkeyJ ?_ (hSv v hv) ?_ ?_ hJ
        · intro x hx y hy h
          have hx' := mem_filter.mp hx
          have hy' := mem_filter.mp hy
          apply hdet x hx'.1 y hy'.1
          intro i hi
          by_cases hii0 : i = i0
          · subst i; rw [hx'.2,hy'.2]
          · exact h i (mem_erase.mpr ⟨hii0,hi⟩)
        · intro x hx
          exact hw x (mem_filter.mp hx).1
        · intro i hi x hx
          exact hr i (mem_of_mem_erase hi) x (mem_filter.mp hx).1
      have hsum : (∑ v ∈ P, Wv v * Real.log (Wv v)) -
          (∑ x ∈ S, w x * Real.log (w x)) ≤
          ∑ v ∈ P, ∑ x ∈ Sv v, w x * ∑ i ∈ J,
            (Real.log (availableReference (Sv v) J key f r i x) - Real.log (r i (f i x))) := by
        calc
          _ = ∑ v ∈ P, weightedFamilyEntropy (Sv v) w := by
            simp only [weightedFamilyEntropy,Finset.sum_sub_distrib]
            rw [← hlog]
          _ ≤ _ := Finset.sum_le_sum hchild
      have hg := weighted_log_sum P Wv (r i0) (hS.image (f i0)) hWv hrP
      rw [← hmass] at hg
      change W * Real.log W - (∑ v ∈ P, Wv v * Real.log (Wv v)) ≤
        -(∑ v ∈ P, Wv v * Real.log (r i0 v)) + W * Real.log R at hg
      change W * Real.log W - (∑ x ∈ S, w x * Real.log (w x)) ≤ _
      rw [hroot]
      linarith

end LatinonEntropy

#print axioms LatinonEntropy.weighted_chain_bound
