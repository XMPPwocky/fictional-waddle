import BoundaryTheorem.ScoreFunctionRatifiable
open BoundaryTheorem.ScoreFunctionRatifiable
-- round 1
#print axioms hasFDerivAt_softmax_apply
#print axioms softmaxDeriv_single
#print axioms score_eq_fderiv_log_softmax
#print axioms reinforce_eq_direct
#print axioms hasFDerivAt_J
#print axioms fderiv_J_single
#print axioms differentiableAt_J
#print axioms reinforce_eq
#print axioms reinforce_eq_zero_iff_const
#print axioms ratifiable_iff_const_of_pos
#print axioms reinforce_eq_zero_iff_ratifiable
#print axioms ratifiable_of_reinforce_eq_zero
#print axioms reinforce_eq_scoreUpdate
#print axioms scoreUpdate_eq_zero_of_ratifiable
#print axioms ratifiable_of_scoreUpdate_eq_zero
#print axioms hasFDerivAt_softmax
#print axioms softmax_zero_fin3
#print axioms AO_J_le
#print axioms AO_J_eq_iff
#print axioms AO_isMaxOn
#print axioms AO_hasFDerivAt_J_zero
#print axioms AO_fderiv_J_zero
#print axioms AO_not_ratifiable
#print axioms AO_reinforce_zero
#print axioms AO_reinforce_ne_zero
#print axioms AO_not_reinforce_stationary
#print axioms AO_indirect_zero
#print axioms newcomb_J
#print axioms newcomb_reinforce_ne_zero
#print axioms newcomb_J_lt
#print axioms newcomb_pure_scoreUpdate_zero
#print axioms newcomb_pure_not_ratifiable
-- round 2: vertex lemma, AO global facts
#print axioms scoreUpdate_single_eq_zero
#print axioms newcomb_pure_scoreUpdate_zero'
#print axioms AO_not_ratifiable_of_decline_pos
#print axioms AO_not_ratifiable_all
#print axioms AO_reinforce_ne_zero_all
#print axioms AO_ratifiable_iff
#print axioms AOratif_simplex
#print axioms AO_Jpol_ratif
#print axioms AO_value_gap
-- round 2: parametrised policies
#print axioms hasFDerivAt_frozen
#print axioms hasFDerivAt_Jp
#print axioms directP_eq_score
#print axioms directP_eq_zero_iff_firstOrderRatifiable
#print axioms directP_eq_zero_iff_orth
#print axioms firstOrderRatifiable_const
#print axioms AO_firstOrderRatifiable_const_not_ratifiable
#print axioms directP_softmax
#print axioms directP_softmax_eq_zero_iff
#print axioms firstOrderRatifiable_softmax_iff
-- round 2: policy-level estimator
#print axioms tendsto_symmDiff
#print axioms tendsto_antithetic
#print axioms isotropic_single
#print axioms tendsto_antithetic_grad
#print axioms tendsto_antithetic_J
#print axioms AO_tendsto_antithetic_zero
-- round 2: boundary limits
#print axioms deriv_limit_eq_zero_of_tendsto
#print axioms sub_eq_log_softmax_sub
#print axioms tendsto_scoreUpdate_of_tendsto
#print axioms limit_const_on_support
