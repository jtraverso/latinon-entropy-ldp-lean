module

public import LatinonBlockVolumes
public import LabelClassification
public import LatinGridBallLowerBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

def latinonPartitionEntropy (W : LatinonMeasure) {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t) : ℝ :=
  finiteTableEntropy (latinonPartitionVolume A B P) (latinonPartitionTable W A B P)

/-- A full-metric ball upper bound for every fixed positive measurable
partition. Its radius and order threshold precede the family of squares. -/
theorem exists_latinon_partition_local_upper (W : LatinonMeasure) {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t)
    (hA : ∀ a, 0 < volume.real (A.cell a)) (hB : ∀ b, 0 < volume.real (B.cell b))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n) (S : Finset (LatinArray n)),
      (∀ L ∈ S, latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*
        (Real.log (n : ℝ)-2+latinonPartitionEntropy W A B P+eta)) := by
  let v := latinonPartitionVolume A B P
  let target := latinonPartitionTable W A B P
  obtain ⟨M,hM,Delta,hDelta,hfinite⟩ := exists_latin_block_local_upper v target
    (latinon_partition_volume_pos A B P hA hB) (eta/2) (half_pos heta)
  obtain ⟨NR,hNR,hround⟩ := exists_uniform_metric_ball_rounding W P r s (Delta/8) (by linarith only [hDelta]) M
  obtain ⟨NL,hNL,hlabels⟩ := exists_label_pair_subquadratic_bound r s (eta/2) (half_pos heta)
  obtain ⟨K,hK⟩ := exists_nat_gt (8/Delta)
  let N := max NR (max NL K)
  have hN : 0 < N := hNR.trans_le (le_max_left _ _)
  refine ⟨Delta/8,by linarith only [hDelta],N,hN,?_⟩
  intro n hn S hball
  have hnpos : 0 < n := hN.trans_le hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hnRound : NR ≤ n := (le_max_left _ _).trans hn
  have hnLabel : NL ≤ n := ((le_max_left NL K).trans (le_max_right NR _)).trans hn
  have hnK : K ≤ n := ((le_max_right NL K).trans (le_max_right NR _)).trans hn
  have hlarge : (8 : ℝ) < (n : ℝ)*Delta :=
    (div_lt_iff₀ hDelta).mp (hK.trans_le (Nat.cast_le.mpr hnK))
  have hinverse : 1/(n : ℝ) < Delta/8 := by
    apply (div_lt_iff₀ hnR).mpr
    nlinarith only [hlarge]
  let Good : ((Fin n → Fin r) × (Fin n → Fin s)) → LatinArray n → Prop := fun ell L =>
    (∀ z, |latinBlockVolume ell.1 ell.2 (P.color n) z-v z| < Delta) ∧
    (∀ z, |latinBlockObservable ell.1 ell.2 (P.color n) z L/(n : ℝ)^2-target z| ≤ Delta/2) ∧
    (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ))
  have hcover : ∀ L ∈ S, ∃ ell, Good ell L := by
    intro L hL
    obtain ⟨row,col,hwindow,hr,hc,hsize⟩ := hround n hnRound A B L (Delta/8) (hball L hL)
    refine ⟨(row,col),?_,?_,hsize⟩
    · intro z
      have hv := rounded_latin_block_volume_error hnpos A B P row col (Delta/8) hr hc z
      change |latinBlockVolume row col (P.color n) z-latinonPartitionVolume A B P z| < Delta
      linarith only [hv,hinverse,hDelta]
    · intro z
      have hw := hwindow z
      change |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
        W.measure.real ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ
          unitSymbolInterval (P.left z.2) (P.right z.2))| ≤ Delta/2
      linarith only [hw,hDelta]
  let bound := Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+latinonPartitionEntropy W A B P+eta/2))
  have hbound : ∀ ell,
      ((@Finset.filter (LatinArray n) (Good ell)
        (fun L => Classical.propDecidable (Good ell L)) S).card : ℝ) ≤ bound := by
    intro ell
    let _ : DecidablePred (Good ell) := fun L => Classical.propDecidable (Good ell L)
    by_cases hF : (S.filter (Good ell)).Nonempty
    · obtain ⟨L,hL⟩ := hF
      have hg := (mem_filter.mp hL).2
      exact hfinite n ell.1 ell.2 (P.color n) (S.filter (Good ell)) hnpos hg.2.2 hg.1
        (fun X hX => (mem_filter.mp hX).2.2.1)
    · have hz : (S.filter (Good ell)).card = 0 :=
        Nat.eq_zero_of_not_pos (fun h => hF (card_pos.mp h))
      rw [hz,Nat.cast_zero]
      exact (Real.exp_pos _).le
  apply (latin_label_cover_count_upper n r s S Good bound hcover hbound).trans
  calc
    _ ≤ Real.exp ((eta/2)*(n : ℝ)^2)*bound :=
      mul_le_mul_of_nonneg_right (hlabels n hnLabel) (Real.exp_pos _).le
    _ = _ := by
      unfold bound
      rw [← Real.exp_add]
      congr 1
      ring

local instance (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

/-- The family counted is ALL labelled squares in the actual open ball. -/
theorem exists_latinon_partition_ball_count_upper (W : LatinonMeasure) {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t)
    (hA : ∀ a, 0 < volume.real (A.cell a)) (hB : ∀ b, 0 < volume.real (B.cell b))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      ((latinonBallLatinFamily (hN.trans_le hn) W delta).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+latinonPartitionEntropy W A B P+eta)) := by
  obtain ⟨delta,hd,N,hN,hcount⟩ := exists_latinon_partition_local_upper W A B P hA hB eta heta
  refine ⟨delta,hd,N,hN,?_⟩
  intro n hn
  exact hcount n hn _ (fun L hL => (mem_filter.mp hL).2)

end LatinonEntropy

#print axioms LatinonEntropy.exists_latinon_partition_local_upper
#print axioms LatinonEntropy.exists_latinon_partition_ball_count_upper
#print axioms LatinonEntropy.abs_mul_unit_le
#print axioms LatinonEntropy.unit_product_three_abs_sub_le
#print axioms LatinonEntropy.finite_class_proportion_bounds
#print axioms LatinonEntropy.latinon_partition_volume_pos
#print axioms LatinonEntropy.rounded_latin_block_volume_error
