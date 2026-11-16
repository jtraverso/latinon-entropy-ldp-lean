module

public import SingleEdgeCounting

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

theorem abs_finset_change_le_sum {J : Type*} [DecidableEq J]
    (E : Finset J) (F : Finset J → ℝ) (eps : J → ℝ)
    (hstep : ∀ S ⊆ E, ∀ j ∈ E, j ∉ S → |F (insert j S)-F S| ≤ eps j) :
    |F E-F ∅| ≤ ∑ j ∈ E, eps j := by
  revert hstep
  induction E using Finset.induction_on with
  | empty => intro _; simp
  | @insert a S ha ih =>
    intro hstep
    have hsmall : ∀ T ⊆ S, ∀ j ∈ S, j ∉ T → |F (insert j T)-F T| ≤ eps j := by
      intro T hT j hj hnot
      exact hstep T (hT.trans (Finset.subset_insert _ _)) j (Finset.mem_insert_of_mem hj) hnot
    calc
      _ ≤ |F (insert a S)-F S|+|F S-F ∅| := abs_sub_le _ _ _
      _ ≤ eps a+∑ j ∈ S, eps j := add_le_add
        (hstep S (Finset.subset_insert _ _) a (Finset.mem_insert_self _ _) ha) (ih hsmall)
      _ = _ := (Finset.sum_insert ha).symm

def hybridEdgeKernel {V : Type*} [DecidableEq V]
    (K H : (V × V) → I × I → ℝ) (S : Finset (V × V)) (e : V × V) : I × I → ℝ :=
  if e ∈ S then H e else K e

theorem hybridEdgeKernel_insert {V : Type*} [DecidableEq V]
    (K H : (V × V) → I × I → ℝ) (S : Finset (V × V)) (a : V × V) :
    hybridEdgeKernel K H (insert a S)=update (hybridEdgeKernel K H S) a (H a) := by
  funext e
  by_cases hea : e=a
  · subst e
    simp only [hybridEdgeKernel,Finset.mem_insert_self,ite_true,update_self]
  · simp only [hybridEdgeKernel,Finset.mem_insert,hea,false_or,update_of_ne hea]

theorem kernelGraphDensity_congr_on {V : Type*} [Fintype V] (E : Finset (V × V))
    (K H : (V × V) → I × I → ℝ) (h : ∀ e ∈ E, K e=H e) :
    kernelGraphDensity E K=kernelGraphDensity E H := by
  apply integral_congr_ae
  apply ae_of_all
  intro x
  unfold kernelGraphProduct
  exact Finset.prod_congr rfl (fun e he => congrFun (h e he) (x e.1,x e.2))

/-- The finite colored counting lemma for pointwise bounded kernels.
Its error is the SUM of the individual cut errors, with constant one. -/
theorem kernelGraphDensity_counting {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hE : NoOppositeEdges E)
    (K H : (V × V) → I × I → ℝ)
    (hKm : ∀ e ∈ E, Measurable (K e)) (hHm : ∀ e ∈ E, Measurable (H e))
    (hKb : ∀ e ∈ E, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1)
    (hHb : ∀ e ∈ E, ∀ p, H e p ∈ Set.Icc (0 : ℝ) 1)
    (eps : (V × V) → ℝ) (hcut : ∀ e ∈ E, KernelCutClose (K e) (H e) (eps e)) :
    |kernelGraphDensity E K-kernelGraphDensity E H| ≤ ∑ e ∈ E, eps e := by
  let F : Finset (V × V) → ℝ := fun S => kernelGraphDensity E (hybridEdgeKernel K H S)
  have hLm (S : Finset (V × V)) (e : V × V) (he : e ∈ E) :
      Measurable (hybridEdgeKernel K H S e) := by
    by_cases heS : e ∈ S
    · simpa only [hybridEdgeKernel,ite_eq_left heS] using hHm e he
    · simpa only [hybridEdgeKernel,ite_eq_right heS] using hKm e he
  have hLb (S : Finset (V × V)) (e : V × V) (he : e ∈ E) (p : I × I) :
      hybridEdgeKernel K H S e p ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases heS : e ∈ S
    · simpa only [hybridEdgeKernel,ite_eq_left heS] using hHb e he p
    · simpa only [hybridEdgeKernel,ite_eq_right heS] using hKb e he p
  have hstep (S : Finset (V × V)) (_ : S ⊆ E) (a : V × V) (ha : a ∈ E) (hnot : a ∉ S) :
      |F (insert a S)-F S| ≤ eps a := by
    have hc : KernelCutClose (hybridEdgeKernel K H S a) (H a) (eps a) := by
      simpa only [hybridEdgeKernel,ite_eq_right hnot] using hcut a ha
    have h := kernelGraphDensity_single_edge E hE (hybridEdgeKernel K H S) (hLm S) (hLb S)
      a ha (H a) (hHm a ha) (hHb a ha) (eps a) hc
    change |kernelGraphDensity E (hybridEdgeKernel K H (insert a S))-
      kernelGraphDensity E (hybridEdgeKernel K H S)| ≤ eps a
    rw [hybridEdgeKernel_insert,abs_sub_comm]
    exact h
  have h := abs_finset_change_le_sum E F eps hstep
  have hfull : F E=kernelGraphDensity E H := by
    apply kernelGraphDensity_congr_on
    intro e he
    simp only [hybridEdgeKernel,ite_eq_left he]
  have hempty : F ∅=kernelGraphDensity E K := by
    apply kernelGraphDensity_congr_on
    intro e _
    simp only [hybridEdgeKernel,Finset.notMem_empty,ite_false]
  rw [hfull,hempty,abs_sub_comm] at h
  exact h

end LatinonEntropy

#print axioms LatinonEntropy.abs_finset_change_le_sum
#print axioms LatinonEntropy.hybridEdgeKernel_insert
#print axioms LatinonEntropy.kernelGraphDensity_congr_on
#print axioms LatinonEntropy.kernelGraphDensity_counting
