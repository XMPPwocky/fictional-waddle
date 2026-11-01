import BoundaryTheorem.Causal
open BoundaryTheorem.Causal

-- Definitions: confirm shapes
#check @causalField
#print causalField
#print IsKantian
#print linResp
#print scalarA

-- Main theorems: statements
#check @hasFDerivAt_causal_potential
#check @linear_iff
#check @potential_iff_of_causal
#check @BoundaryTheorem.Potential.potential_iff
#check @homoMoralis_not_conservative
#check @graded_hasFDerivAt
#check @operator_iff

-- Axioms
#print axioms hasFDerivAt_causal_potential
#print axioms conservative_of_isKantian
#print axioms causalField_testFamily
#print axioms cross_eq
#print axioms linear_iff
#print axioms graded_hasFDerivAt
#print axioms homoMoralis_not_conservative
#print axioms homoMoralis_field_eq
#print axioms homoMoralis_not_conservative_fin2
#print axioms field_eq_causalField
#print axioms isKantian_iff
#print axioms potential_iff_of_causal
#print axioms conservative_of_r_zero
#print axioms not_kantian_but_conservative_r_zero
#print axioms conservative_dim_one
#print axioms not_kantian_but_conservative_dim_one
#print axioms continuous_causalField
#print axioms op_cross
#print axioms eq_smul_id_of_symm
#print axioms op_self
#print axioms op_pair
#print axioms operator_iff
#print axioms conservative_rank_one
#print axioms rank_one_counterexample
