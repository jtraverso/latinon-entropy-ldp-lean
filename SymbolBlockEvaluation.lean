module

public import LatinSymbolPermutations
public import FiniteAverages
public import Mathlib.Data.Fintype.Perm

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def symbolEvalProbability {n q : ℕ} (color : Fin n → Fin q) (a z : Fin n) : ℝ :=
  finiteMean (fun g : symbolBlockStabilizer color => if g.val a = z then 1 else 0)

theorem symbol_eval_probability_equal {n q : ℕ} (color : Fin n → Fin q)
    (a b c : Fin n) (hbc : color b = color c) :
    symbolEvalProbability color a b = symbolEvalProbability color a c := by
  let s : symbolBlockStabilizer color := ⟨Equiv.swap b c,swap_mem_symbolBlockStabilizer color b c hbc⟩
  let e := Equiv.mulLeft s
  let F := fun g : symbolBlockStabilizer color => if g.val a = c then (1 : ℝ) else 0
  have heq : ∀ g : symbolBlockStabilizer color,
      Equiv.swap b c (g.val a) = c ↔ g.val a = b := by
    intro g
    constructor
    · intro he
      exact (Equiv.swap b c).injective (he.trans (Equiv.swap_apply_left b c).symm)
    · intro he
      rw [he,Equiv.swap_apply_left]
  have hfun : (fun g : symbolBlockStabilizer color => F (e g)) =
      (fun g => if g.val a = b then (1 : ℝ) else 0) := by
    funext g
    by_cases hgb : g.val a = b
    · have hout : (e g).val a = c := by
        simp only [e,s,Equiv.coe_mulLeft,Subgroup.coe_mul,Equiv.Perm.mul_apply,hgb,
          Equiv.swap_apply_left]
      simp only [F,hout,hgb,ite_true]
    · have hout : (e g).val a ≠ c := by
        intro hc
        have hx : Equiv.swap b c (g.val a) = c := by
          simpa only [e,s,Equiv.coe_mulLeft,Subgroup.coe_mul,Equiv.Perm.mul_apply] using hc
        exact hgb ((heq g).mp hx)
      simp only [F,hout,hgb,ite_false]
  have h := finiteMean_equiv e F
  rw [hfun] at h
  exact h

theorem symbol_eval_probability_total {n q : ℕ} (color : Fin n → Fin q) (a : Fin n) :
    (∑ z : Fin n, symbolEvalProbability color a z) = 1 := by
  let : Nonempty (symbolBlockStabilizer color) := ⟨1⟩
  unfold symbolEvalProbability
  rw [← finiteMean_sum]
  have hfun : (fun g : symbolBlockStabilizer color => ∑ z : Fin n,
      if g.val a = z then (1 : ℝ) else 0) = (fun _ => (1 : ℝ)) := by
    funext g
    simp
  rw [hfun,finiteMean_const]

def symbolColorFiber {n q : ℕ} (color : Fin n → Fin q) (a : Fin n) : Finset (Fin n) :=
  univ.filter (fun z => color z = color a)

theorem symbol_eval_probability_outside {n q : ℕ} (color : Fin n → Fin q)
    (a z : Fin n) (hz : color z ≠ color a) : symbolEvalProbability color a z = 0 := by
  let : Nonempty (symbolBlockStabilizer color) := ⟨1⟩
  have hne : ∀ g : symbolBlockStabilizer color, g.val a ≠ z := by
    intro g he
    exact hz ((congrArg color he).symm.trans (g.property a))
  have hfun : (fun g : symbolBlockStabilizer color => if g.val a = z then (1 : ℝ) else 0) =
      (fun _ => (0 : ℝ)) := by
    funext g
    simp only [hne g,ite_false]
  unfold symbolEvalProbability
  rw [hfun,finiteMean_const]

theorem symbol_eval_probability_uniform {n q : ℕ} (color : Fin n → Fin q) (a z : Fin n) :
    symbolEvalProbability color a z =
      if color z = color a then 1/((symbolColorFiber color a).card : ℝ) else 0 := by
  let F := symbolColorFiber color a
  have hconst : ∀ b ∈ F, symbolEvalProbability color a b = symbolEvalProbability color a a := by
    intro b hb
    have hc : color b = color a := by
      simpa only [F,symbolColorFiber,mem_filter,mem_univ,true_and] using hb
    exact symbol_eval_probability_equal color a b a hc
  have hsum : (∑ b ∈ F, symbolEvalProbability color a b) = 1 := by
    calc
      _ = ∑ b : Fin n, symbolEvalProbability color a b := by
        apply sum_subset (subset_univ F)
        intro b _ hb
        have hc : color b ≠ color a := by
          simpa only [F,symbolColorFiber,mem_filter,mem_univ,true_and] using hb
        exact symbol_eval_probability_outside color a b hc
      _ = 1 := symbol_eval_probability_total color a
  have he : (∑ b ∈ F, symbolEvalProbability color a b) =
      (F.card : ℝ)*symbolEvalProbability color a a := by
    calc
      _ = ∑ _b ∈ F, symbolEvalProbability color a a := sum_congr rfl (fun b hb => hconst b hb)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hpos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (card_pos.mpr
    ⟨a,by simp only [F,symbolColorFiber,mem_filter,mem_univ,true_and]⟩)
  have ha : symbolEvalProbability color a a = 1/(F.card : ℝ) := by
    apply (eq_div_iff hpos.ne').mpr
    nlinarith only [hsum,he]
  by_cases hz : color z = color a
  · simp only [hz,ite_true]
    exact (symbol_eval_probability_equal color a z a hz).trans ha
  · simp only [hz,ite_false]
    exact symbol_eval_probability_outside color a z hz

end LatinonEntropy

#print axioms LatinonEntropy.symbol_eval_probability_equal
#print axioms LatinonEntropy.symbol_eval_probability_total
#print axioms LatinonEntropy.symbol_eval_probability_uniform
