module

public import KernelGraphAEBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

theorem integral_resampleCoordinate {V : Type*} [Fintype V] [DecidableEq V]
    (u : V) (f : (V → I) → ℝ) (hf : Integrable f (vertexSampleLaw V)) :
    (∫ x, f x ∂vertexSampleLaw V)=
      ∫ x, ∫ t, f (resampleCoordinate u (x,t)) ∂volume ∂vertexSampleLaw V := by
  have hm := resampleCoordinate_preserving u
  have hfmap : AEStronglyMeasurable f
      (Measure.map (resampleCoordinate u) ((vertexSampleLaw V).prod volume)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hfmap
  rw [hm.map_eq] at he
  exact he.trans (integral_prod _ (hm.integrable_comp_of_integrable hf))

theorem integral_vertexPair {V : Type*} [Fintype V] (u v : V) (huv : u ≠ v)
    (f : I × I → ℝ) (hf : Integrable f unitSquareVolume) :
    (∫ x, f (x u,x v) ∂vertexSampleLaw V)=∫ p, f p ∂unitSquareVolume := by
  have hm := vertexPair_preserving u v huv
  have hfmap : AEStronglyMeasurable f (Measure.map (fun x : V → I => (x u,x v)) (vertexSampleLaw V)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hfmap
  rw [hm.map_eq] at he
  exact he.symm

/-- A leaf coordinate can be integrated out using an a.e. constant kernel
margin. The other factor may share the leaf's other endpoint. -/
theorem integral_vertex_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (u v r s : V) (huv : u ≠ v) (hru : r ≠ u) (hsu : s ≠ u)
    (f g : I × I → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (hgb : ∀ p, g p ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hmean : (fun y => ∫ t, f (t,y) ∂volume)=ᵐ[volume] (fun _ : I => c)) :
    (∫ x, f (x u,x v)*g (x r,x s) ∂vertexSampleLaw V)=
      c*(∫ x, g (x r,x s) ∂vertexSampleLaw V) := by
  let F : (V → I) → ℝ := fun x => f (x u,x v)*g (x r,x s)
  have hFi : Integrable F (vertexSampleLaw V) := by
    apply Integrable.of_mem_Icc 0 1
      ((hfm.comp ((measurable_pi_apply u).prodMk (measurable_pi_apply v))).mul
        (hgm.comp ((measurable_pi_apply r).prodMk (measurable_pi_apply s)))).aemeasurable
    apply ae_of_all
    intro x
    exact ⟨mul_nonneg (hfb _).1 (hgb _).1,
      (mul_le_mul_of_nonneg_right (hfb _).2 (hgb _).1).trans
        (by simpa only [one_mul] using (hgb _).2)⟩
  have hm := (measurePreserving_eval (fun _ : V => (volume : Measure I)) v).quasiMeasurePreserving.ae hmean
  have hpoint (x : V → I) (t : I) :
      F (resampleCoordinate u (x,t))=f (t,x v)*g (x r,x s) := by
    simp only [F,resampleCoordinate,update_self,update_of_ne huv.symm,
      update_of_ne hru,update_of_ne hsu]
  calc
    _ = ∫ x, ∫ t, F (resampleCoordinate u (x,t)) ∂volume ∂vertexSampleLaw V :=
      integral_resampleCoordinate u F hFi
    _ = ∫ x, c*g (x r,x s) ∂vertexSampleLaw V := by
      apply integral_congr_ae
      filter_upwards [hm] with x hx
      simp_rw [hpoint,integral_mul_const]
      rw [hx]
    _ = _ := integral_const_mul _ _

end LatinonEntropy

#print axioms LatinonEntropy.integral_resampleCoordinate
#print axioms LatinonEntropy.integral_vertexPair
#print axioms LatinonEntropy.integral_vertex_leaf
