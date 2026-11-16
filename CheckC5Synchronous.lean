module

/- Axiom audit of common-alignment completeness and actual symbol-grid control. -/
public import LatinonSynchronousAction
public import LatinonSynchronousDistance
public import LatinonSynchronousCompleteness
public import SymbolIntervalGridApproximation
public import LatinonSymbolGridControl

@[expose] public section

#print axioms LatinonEntropy.latinonMeasure_eq_of_measure_order_eq
#print axioms LatinonEntropy.synchronousRelabel
#print axioms LatinonEntropy.synchronousRelabel_refl
#print axioms LatinonEntropy.synchronousRelabel_comp
#print axioms LatinonEntropy.synchronousRelabel_inverse
#print axioms LatinonEntropy.rawCutCost_synchronous_invariant
#print axioms LatinonEntropy.rawCutCost_synchronous_eq_alignmentCost
#print axioms LatinonEntropy.synchronousRelabel_full_distance_zero
#print axioms LatinonEntropy.synchronousCost_range_nonempty
#print axioms LatinonEntropy.synchronousCost_range_bddBelow
#print axioms LatinonEntropy.synchronousCutDistance_nonneg
#print axioms LatinonEntropy.synchronousCutDistance_le_cost
#print axioms LatinonEntropy.synchronousCutDistance_le_rawCost
#print axioms LatinonEntropy.synchronousCutDistance_self
#print axioms LatinonEntropy.synchronousCutDistance_symm
#print axioms LatinonEntropy.exists_synchronousCost_lt
#print axioms LatinonEntropy.synchronousCutDistance_triangle
#print axioms LatinonEntropy.latinonCutDistance_le_synchronous
#print axioms LatinonEntropy.synchronousLatinon_forget_lipschitz
#print axioms LatinonEntropy.synchronousLatinon_forget_continuous
#print axioms LatinonEntropy.synchronousCutDistance_relabel_zero
#print axioms LatinonEntropy.rawLatinonPseudoMetric
#print axioms LatinonEntropy.synchronousLatinon_complete
#print axioms LatinonEntropy.symbolGridUnion_measurable
#print axioms LatinonEntropy.lebesgueGridCell_point_lt
#print axioms LatinonEntropy.exists_symbol_grid_inner_approximation
#print axioms LatinonEntropy.symbol_grid_inner_approximation_error
#print axioms LatinonEntropy.latinon_box_inner_symbol_error
#print axioms LatinonEntropy.latinon_box_grid_union_sum
#print axioms LatinonEntropy.latinon_grid_union_difference_le
#print axioms LatinonEntropy.measureCut_le_symbol_grid_tests
