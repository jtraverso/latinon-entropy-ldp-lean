module

public import LatinonPatternContinuity
public import GridCoordinateIndex
public import FiniteLatinMeasureMargins

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem grid_cell_inter_real {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell j)=
      if i=j then 1/(n : ℝ) else 0 := by
  by_cases hij : i=j
  · subst j
    calc
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell i) =
          1/(n : ℝ) := by rw [Set.inter_self,lebesgueGridCell_mass hn i]
      _ = (if i=i then 1/(n : ℝ) else 0) := (ite_eq_left rfl).symm
  · have he : lebesgueGridCell i ∩ lebesgueGridCell j=∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (Set.disjoint_left.mp (lebesgueGridCell_disjoint hn i j hij) hx.1 hx.2)
      · intro hx
        exact False.elim hx
    calc
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell j) =
          (0 : ℝ) := by rw [he,measureReal_empty]
      _ = (if i=j then 1/(n : ℝ) else 0) := (ite_eq_right hij).symm

theorem finiteLatinMeasure_grid_box {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (i j s : Fin n) :
    (finiteLatinMeasure L).real ((lebesgueGridCell i ×ˢ lebesgueGridCell j) ×ˢ lebesgueGridCell s)=
      if L.val i j=s then (1/(n : ℝ))^2 else 0 := by
  have hne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  rw [finiteLatinMeasure_real_box]
  have hsum : (∑ x : Fin n, ∑ y : Fin n,
      (volume : Measure I).real (lebesgueGridCell i ∩ lebesgueGridCell x)*
        volume.real (lebesgueGridCell j ∩ lebesgueGridCell y)*
          volume.real (lebesgueGridCell s ∩ lebesgueGridCell (L.val x y)))=
      volume.real (lebesgueGridCell i ∩ lebesgueGridCell i)*
        volume.real (lebesgueGridCell j ∩ lebesgueGridCell j)*
          volume.real (lebesgueGridCell s ∩ lebesgueGridCell (L.val i j)) := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · intro y _ hy
        rw [grid_cell_inter_real hn j y,ite_eq_right (Ne.symm hy)]
        simp only [mul_zero,zero_mul]
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro x _ hx
      rw [grid_cell_inter_real hn i x,ite_eq_right (Ne.symm hx)]
      simp only [zero_mul,Finset.sum_const_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  rw [hsum,Set.inter_self,Set.inter_self,lebesgueGridCell_mass hn i,lebesgueGridCell_mass hn j]
  by_cases hs : L.val i j=s
  · rw [ite_eq_left hs,hs,Set.inter_self,lebesgueGridCell_mass hn s]
    field_simp [hne]
  · rw [grid_cell_inter_real hn s (L.val i j),ite_eq_right (Ne.symm hs),ite_eq_right hs]
    simp only [mul_zero]

theorem bounded_integral_extreme_ae {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) (hfm : Measurable f)
    (hfb : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ) (hc : c=0 ∨ c=1)
    (hmean : (∫ x, f x ∂μ)=μ.real Set.univ*c) : f=ᵐ[μ] (fun _ => c) := by
  have hi := Integrable.of_mem_Icc 0 1 hfm.aemeasurable hfb
  rcases hc with rfl|rfl
  · have hn : 0 ≤ᵐ[μ] f := hfb.mono (fun _ hx => hx.1)
    apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    simpa only [mul_zero] using hmean
  · have hgi : Integrable (fun x => 1-f x) μ := (integrable_const 1).sub hi
    have hgn : 0 ≤ᵐ[μ] (fun x => 1-f x) := hfb.mono (fun _ hx => sub_nonneg.mpr hx.2)
    have hzero : (∫ x, 1-f x ∂μ)=0 := by
      rw [integral_sub (integrable_const 1) hi,integral_const]
      simp only [smul_eq_mul,mul_one] at hmean ⊢
      linarith
    have hz := (integral_eq_zero_iff_of_nonneg_ae hgn hgi).mp hzero
    filter_upwards [hz] with x hx
    change 1-f x=0 at hx
    linarith

theorem finite_symbol_grid_probability_on_box {n : ℕ} (hn : 0 < n)
    (L : LatinArray n) (i j s : Fin n) :
    ∀ᵐ p ∂unitSquareVolume, p ∈ lebesgueGridCell i ×ˢ lebesgueGridCell j →
      (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
        if L.val i j=s then (1 : ℝ) else 0 := by
  let W := latinArrayToLatinonMeasure hn L
  let S := lebesgueGridCell i ×ˢ lebesgueGridCell j
  let μ := unitSquareVolume.restrict S
  let f : I × I → ℝ := fun p => (latinonSymbolKernel W p).real (lebesgueGridCell s)
  have hS : MeasurableSet S := (lebesgueGridCell_measurable i).prod (lebesgueGridCell_measurable j)
  have hμ : μ.real Set.univ=(1/(n : ℝ))^2 := by
    change ((unitSquareVolume.restrict S) Set.univ).toReal=_
    rw [Measure.restrict_apply_univ]
    change unitSquareVolume.real (lebesgueGridCell i ×ˢ lebesgueGridCell j)=_
    rw [measureReal_prod_prod,lebesgueGridCell_mass hn i,lebesgueGridCell_mass hn j]
    ring
  have hint : (∫ p, f p ∂μ)=if L.val i j=s then (1/(n : ℝ))^2 else 0 := by
    change (∫ p in S, (latinonSymbolKernel W p).real (lebesgueGridCell s) ∂unitSquareVolume)=_
    rw [latinonSymbolKernel_real_rectangle W _ _ _ (lebesgueGridCell_measurable i)
      (lebesgueGridCell_measurable j) (lebesgueGridCell_measurable s)]
    exact finiteLatinMeasure_grid_box hn L i j s
  have he : f=ᵐ[μ] (fun _ => if L.val i j=s then (1 : ℝ) else 0) := by
    apply bounded_integral_extreme_ae μ f
      (measurable_latinonSymbolKernel_event W _ (lebesgueGridCell_measurable s)).ennreal_toReal
      (ae_of_all _ (latinonSymbolKernel_real_mem_Icc W _))
    · by_cases hs : L.val i j=s <;> simp [hs]
    · rw [hint,hμ]
      by_cases hs : L.val i j=s <;> simp [hs]
  exact (ae_restrict_iff' hS).mp he

/-- The actual conditional symbol kernel of the embedded square assigns
probability one to its matrix entry's grid bin, almost everywhere. -/
theorem finite_symbol_grid_probability {n : ℕ} (hn : 0 < n) (L : LatinArray n) :
    ∀ᵐ p ∂unitSquareVolume, ∀ s : Fin n,
      (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
        if L.val (unitGridIndex n hn p.1) (unitGridIndex n hn p.2)=s then (1 : ℝ) else 0 := by
  have hbox : ∀ᵐ p ∂unitSquareVolume, ∀ i j s : Fin n,
      p ∈ lebesgueGridCell i ×ˢ lebesgueGridCell j →
        (latinonSymbolKernel (latinArrayToLatinonMeasure hn L) p).real (lebesgueGridCell s)=
          if L.val i j=s then (1 : ℝ) else 0 := by
    simp only [ae_all_iff]
    exact fun i j s => finite_symbol_grid_probability_on_box hn L i j s
  have hx := (measurePreserving_fst (μ := (volume : Measure I)) (ν := (volume : Measure I))).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  have hy := (measurePreserving_snd (μ := (volume : Measure I)) (ν := (volume : Measure I))).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  filter_upwards [hbox,hx,hy] with p hp hpx hpy
  obtain ⟨i,hi⟩ := hpx
  obtain ⟨j,hj⟩ := hpy
  intro s
  rw [unitGridIndex_of_mem hn hi,unitGridIndex_of_mem hn hj]
  exact hp i j s ⟨hi,hj⟩

end LatinonEntropy

#print axioms LatinonEntropy.grid_cell_inter_real
#print axioms LatinonEntropy.finiteLatinMeasure_grid_box
#print axioms LatinonEntropy.bounded_integral_extreme_ae
#print axioms LatinonEntropy.finite_symbol_grid_probability_on_box
#print axioms LatinonEntropy.finite_symbol_grid_probability
