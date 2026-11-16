module

public import HistoryMartingale
public import StoppedAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem finite_abs_mean_sq_le {I : Type*} [Fintype I] (p X : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    (∑ i, p i*|X i|)^2 ≤ ∑ i, p i*(X i)^2 := by
  let A := ∑ i, p i*|X i|
  have hnonneg : 0 ≤ ∑ i, p i*(|X i|-A)^2 :=
    sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  have he : ∀ i, p i*(|X i|-A)^2 = p i*(X i)^2-(2*A)*(p i*|X i|)+A^2*p i := by
    intro i
    rw [show p i*(|X i|-A)^2 = p i*|X i|^2-(2*A)*(p i*|X i|)+A^2*p i by ring,sq_abs]
  simp_rw [he] at hnonneg
  rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hmass,mul_one] at hnonneg
  change A^2 ≤ _
  change 0 ≤ (∑ i, p i*(X i)^2)-(2*A)*A+A^2 at hnonneg
  nlinarith only [hnonneg]

theorem history_abs_mean_le_sqrt {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (t : ℕ) (X : List Ω → ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hsecond : historyExpectation K t (fun h => (X h)^2) ≤ V) :
    historyExpectation K t (fun h => |X h|) ≤ Real.sqrt V := by
  let S := histories Ω t
  have hmass : (∑ h : S, historyWeight K h) = 1 := by
    rw [Finset.sum_coe_sort]
    exact historyWeight_total K t
  have hs := finite_abs_mean_sq_le (fun h : S => historyWeight K h) (fun h : S => X h)
    (fun h => historyWeight_nonneg K h) hmass
  have hs' : (historyExpectation K t (fun h => |X h|))^2 ≤
      historyExpectation K t (fun h => (X h)^2) := by
    have habs : (∑ h : S, historyWeight K h*|X h|) =
        ∑ h ∈ S, historyWeight K h*|X h| :=
      Finset.sum_coe_sort S (fun h => historyWeight K h*|X h|)
    have hsq : (∑ h : S, historyWeight K h*(X h)^2) =
        ∑ h ∈ S, historyWeight K h*(X h)^2 :=
      Finset.sum_coe_sort S (fun h => historyWeight K h*(X h)^2)
    rw [habs,hsq] at hs
    exact hs
  have hroot := Real.sq_sqrt hV
  have hroot0 := Real.sqrt_nonneg V
  have ha : 0 ≤ historyExpectation K t (fun h => |X h|) :=
    sum_nonneg (fun h _ => mul_nonneg (historyWeight_nonneg K h) (abs_nonneg _))
  nlinarith only [hs',hsecond,hroot,hroot0,ha]

def killedCenteredValue {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω)
    (Good : List Ω → Prop) (V : List Ω → Ω → ℝ) (h : List Ω) (a : Ω) : ℝ :=
  if historyLive Good h then V h a-(∑ b, K.transition h b*V h b) else 0

theorem killedCenteredValue_mean_zero {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω)
    (Good : List Ω → Prop) (V : List Ω → Ω → ℝ) (h : List Ω) :
    (∑ a, K.transition h a*killedCenteredValue K Good V h a) = 0 := by
  by_cases hlive : historyLive Good h
  · simp only [killedCenteredValue,hlive,ite_true,mul_sub,sum_sub_distrib,← sum_mul,K.total,one_mul,sub_self]
  · simp only [killedCenteredValue,hlive,ite_false,mul_zero,sum_const_zero]

theorem killedCenteredValue_abs_le {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω)
    (Good : List Ω → Prop) (V : List Ω → Ω → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hV : ∀ h a, 0 ≤ V h a ∧ V h a ≤ b) (h : List Ω) (a : Ω) :
    |killedCenteredValue K Good V h a| ≤ b := by
  have hlo : 0 ≤ ∑ a, K.transition h a*V h a :=
    sum_nonneg (fun a _ => mul_nonneg (K.nonneg h a) (hV h a).1)
  have hhi : (∑ a, K.transition h a*V h a) ≤ b := by
    calc
      _ ≤ ∑ a, K.transition h a*b :=
        sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hV h a).2 (K.nonneg h a))
      _ = b := by rw [← sum_mul,K.total,one_mul]
  by_cases hlive : historyLive Good h
  · simp only [killedCenteredValue,hlive,ite_true]
    exact abs_le.mpr ⟨by linarith [(hV h a).1],by linarith [(hV h a).2]⟩
  · simpa only [killedCenteredValue,hlive,ite_false,abs_zero] using hb

theorem killed_centered_path_abs_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Good : List Ω → Prop) (V : List Ω → Ω → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hV : ∀ h a, 0 ≤ V h a ∧ V h a ≤ b) (t : ℕ) :
    historyExpectation K t (fun h => |pathSum (killedCenteredValue K Good V) h|) ≤
      Real.sqrt ((t : ℝ)*b^2) := by
  have hvar : ∀ h, (∑ a, K.transition h a*(killedCenteredValue K Good V h a)^2) ≤ b^2 := by
    intro h
    calc
      _ ≤ ∑ a, K.transition h a*b^2 := sum_le_sum (fun a _ =>
        mul_le_mul_of_nonneg_left (by
          have ha := (sq_le_sq₀ (abs_nonneg _) hb).mpr (killedCenteredValue_abs_le K Good V b hb hV h a)
          simpa only [sq_abs] using ha) (K.nonneg h a))
      _ = _ := by rw [← sum_mul,K.total,one_mul]
  have hsecond := history_pathSum_second_moment_le K (killedCenteredValue K Good V)
    (fun _ => b^2) (killedCenteredValue_mean_zero K Good V) hvar t
  apply history_abs_mean_le_sqrt K t _ _ (by positivity)
  simpa using hsecond

end LatinonEntropy

#print axioms LatinonEntropy.killed_centered_path_abs_le
