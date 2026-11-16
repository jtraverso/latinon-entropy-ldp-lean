module

public import UnitIntervalBand
public import OrderPermutationL1

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def unitOrderDisagreement (f g : I → I) : Set (I × I) :=
  {p | (f p.1 < f p.2 ∧ ¬ g p.1 < g p.2) ∨ (g p.1 < g p.2 ∧ ¬ f p.1 < f p.2)}

theorem unitOrderDisagreement_measurable (f g : I → I) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (unitOrderDisagreement f g) := by
  unfold unitOrderDisagreement
  have hF := measurableSet_lt (hf.comp measurable_fst) (hf.comp measurable_snd)
  have hG := measurableSet_lt (hg.comp measurable_fst) (hg.comp measurable_snd)
  exact (hF.inter hG.compl).union (hG.inter hF.compl)

def unitMapBad (f g : I → I) (t : ℝ) : Set I := {u | t ≤ |(f u : ℝ)-(g u : ℝ)|}

theorem unitMapBad_markov (f g : I → I) (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    t*(volume : Measure I).real (unitMapBad f g t) ≤ ∫ u : I, |(f u : ℝ)-(g u : ℝ)| :=
  mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_unit_coordinate f hf).sub (integrable_unit_coordinate g hg)).abs t

theorem unitOrderDisagreement_cover (f g : I → I) (t : ℝ) :
    unitOrderDisagreement f g ⊆
      ({p : I × I | |(f p.1 : ℝ)-(f p.2 : ℝ)| ≤ 2*t} ∪
        (unitMapBad f g t ×ˢ Set.univ)) ∪ (Set.univ ×ˢ unitMapBad f g t) := by
  intro p hp
  by_cases hb : |(f p.1 : ℝ)-(f p.2 : ℝ)| ≤ 2*t
  · exact Or.inl (Or.inl hb)
  by_cases hu : t ≤ |(f p.1 : ℝ)-(g p.1 : ℝ)|
  · exact Or.inl (Or.inr ⟨hu,Set.mem_univ _⟩)
  by_cases hv : t ≤ |(f p.2 : ℝ)-(g p.2 : ℝ)|
  · exact Or.inr ⟨Set.mem_univ _,hv⟩
  have hU := abs_lt.mp (lt_of_not_ge hu)
  have hV := abs_lt.mp (lt_of_not_ge hv)
  exfalso
  apply hb
  rcases hp with ⟨hF,hG⟩ | ⟨hG,hF⟩
  · have hfR : (f p.1 : ℝ) ≤ (f p.2 : ℝ) := hF.le
    have hgR : (g p.2 : ℝ) ≤ (g p.1 : ℝ) := le_of_not_gt hG
    rw [abs_of_nonpos (sub_nonpos.mpr hfR)]
    linarith only [hU.1,hV.2,hgR]
  · have hfR : (f p.2 : ℝ) ≤ (f p.1 : ℝ) := le_of_not_gt hF
    have hgR : (g p.1 : ℝ) ≤ (g p.2 : ℝ) := hG.le
    rw [abs_of_nonneg (sub_nonneg.mpr hfR)]
    linarith only [hU.2,hV.1,hgR]

/-- Quantitative control of the ACTUAL order relation,not just the map
values. Only the first map needs a uniform push-forward. -/
theorem unitOrderDisagreement_L1_bound (f g : I → I)
    (hf : MeasurePreserving f volume volume) (hg : Measurable g) (t : ℝ) (ht : 0 < t) :
    t*((volume : Measure I).prod volume).real (unitOrderDisagreement f g) ≤
      4*t^2+2*(∫ u : I, |(f u : ℝ)-(g u : ℝ)|) := by
  let mu : Measure (I × I) := (volume : Measure I).prod volume
  let B := unitMapBad f g t
  let C := {p : I × I | |(f p.1 : ℝ)-(f p.2 : ℝ)| ≤ 2*t}
  have hcover := measureReal_mono (μ := mu) (unitOrderDisagreement_cover f g t)
  change mu.real (unitOrderDisagreement f g) ≤
    mu.real ((C ∪ (B ×ˢ Set.univ)) ∪ (Set.univ ×ˢ B)) at hcover
  have hu1 := measureReal_union_le (μ := mu) (C ∪ (B ×ˢ Set.univ)) (Set.univ ×ˢ B)
  have hu2 := measureReal_union_le (μ := mu) C (B ×ˢ Set.univ)
  have hleft : mu.real (B ×ˢ Set.univ) = (volume : Measure I).real B := by
    change ((volume : Measure I).prod volume).real (B ×ˢ Set.univ) = _
    rw [measureReal_prod_prod,probReal_univ,mul_one]
  have hright : mu.real (Set.univ ×ˢ B) = (volume : Measure I).real B := by
    change ((volume : Measure I).prod volume).real (Set.univ ×ˢ B) = _
    rw [measureReal_prod_prod,probReal_univ,one_mul]
  simp only [hleft,hright] at hu1 hu2
  have hband := mp_unitBand_mass f hf (2*t) (by linarith only [ht])
  have hbad := unitMapBad_markov f g hf.measurable hg t
  have hmass : mu.real (unitOrderDisagreement f g) ≤ 4*t+2*(volume : Measure I).real B := by
    change mu.real C ≤ 2*(2*t) at hband
    linarith only [hcover,hu1,hu2,hband]
  have hscaled := mul_le_mul_of_nonneg_left hmass ht.le
  change t*(volume : Measure I).real B ≤ _ at hbad
  dsimp only [mu] at hscaled
  nlinarith only [hscaled,hbad]

end LatinonEntropy

#print axioms LatinonEntropy.unitOrderDisagreement_measurable
#print axioms LatinonEntropy.unitMapBad_markov
#print axioms LatinonEntropy.unitOrderDisagreement_cover
#print axioms LatinonEntropy.unitOrderDisagreement_L1_bound
