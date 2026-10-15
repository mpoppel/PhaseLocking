import PhaseLocking

/-!
Axioms behind every theorem named in the README. Run with

    lake env lean Axioms.lean

after `lake build`. Each line should list only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms gate_model_eq_design
#print axioms ancillaModel_trig
#print axioms dataJac_eq_design_mul
#print axioms design_gram_eqGrid
#print axioms grid_singular_bounds
#print axioms coupling_depth
#print axioms gate_tangent_collinear
#print axioms gate_phase_locking
#print axioms gate_tangent_local
#print axioms gate_tangent_trig
#print axioms gate_envelope_trig
#print axioms phase_locking
#print axioms perp_unit_eq_phase_T
#print axioms perp_phase_invariant
#print axioms envelope_steepest_ascent
#print axioms multi_qubit_phase_locking
#print axioms multi_qubit_envelopes
#print axioms multi_qubit_envelope_normSq
#print axioms multi_qubit_envelope_shift
#print axioms multi_qubit_adapted_basis
#print axioms multi_qubit_frame_change
#print axioms tangent_span_frame_invariant
#print axioms gate_coeffJac_factorisation
#print axioms serial_class_eq
#print axioms ancilla_class_eq
#print axioms serial_generic_full_rank
#print axioms ancilla_generic_full_rank
#print axioms serial_tangent_rank_le
#print axioms serial_tangent_rank_generic
#print axioms ancilla_tangent_rank_generic
#print axioms parallel2_tangent_rank_le
#print axioms parallel2_tangent_rank_generic
#print axioms T_first_column
#print axioms serial_tangent_rank_eq_rank_H
#print axioms gate_readout_rotation
#print axioms serial_readout_mem_span
#print axioms envelope_normSq
#print axioms gate_envelope_normSq
#print axioms serial_no_spare_direction
#print axioms serial_readout_in_kernel
#print axioms serial_no_spare_direction_generic
#print axioms serial_no_spare_direction_target
#print axioms serial_critical_targets_null
#print axioms serial_targets_contain_ball
#print axioms stationary_is_least_squares
#print axioms serial_stationary_is_least_squares
#print axioms ancilla_stationary_is_least_squares
#print axioms genericity
#print axioms stacked_gates_rescale
#print axioms pauli_basis_props
#print axioms pauliWord_basis_props
#print axioms genModel_reframe
#print axioms reframe_mem_SU
#print axioms reframe_reframe
#print axioms gateModel_eq_genModel
#print axioms ancillaGateModel_eq_genModel
#print axioms readout_commutant_one_qubit
#print axioms readout_commutant_two_qubits
#print axioms readoutWord_commute
#print axioms readoutWord_linearIndependent
#print axioms readout_rotation_first_order
#print axioms unchanged_directions_finrank
#print axioms serialUnchanged_finrank
#print axioms ancillaUnchanged_finrank
#print axioms serialUnchanged_eq_span
#print axioms ancilla_gate_phase_locking
#print axioms ancillaRotations_finrank_le
#print axioms ancillaRotations_le_unchanged
#print axioms ancilla_spare_ge
#print axioms ancilla_spare_generic
#print axioms parallel2_gate_phase_locking
#print axioms parallel2_spare_ge
#print axioms parallel2_spare_generic
#print axioms Tpaper_eq_neg_T
#print axioms envelope_product_sign_invariant
#print axioms gqspHyp_of_MW
#print axioms genState_reframe
