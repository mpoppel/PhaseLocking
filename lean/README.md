# Lean formalisation (supplementary material)

`PhaseLocking.lean` states and proves, in Lean 4 with Mathlib, every lemma, proposition, remark and corollary of
Sections 3 and 4 and of Appendix B of the paper: Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Remark 4.3, Eq. (2),
Proposition 4.4, Corollary 4.5, Lemma B.1, Lemma B.2 and Lemma B.3. Section 24 of the file adds statements that the
paper makes in running text; Section 25 states the cited generalised QSP theorem in its authors' convention and
derives the form used in the file. Appendix C of the paper says what is and what is not formalised;
this file maps each result to its Lean theorems and states the conventions of the Lean file.

The proofs were developed with the automated prover Aristotle and are checked by the Lean kernel. The file contains
no `sorry`, and nothing is added as an axiom.

## Build

Requires `elan`. Toolchain: Lean v4.28.0 (`lean-toolchain`); Mathlib is pinned in `lake-manifest.json`.

    lake exe cache get
    lake build
    lake env lean Axioms.lean

The last command prints the axioms behind each theorem of the table below. Each line should list only `propext`,
`Classical.choice` and `Quot.sound`.

## Files

| File | Content |
|---|---|
| `PhaseLocking.lean` | the formalisation; its module docstring maps the sections of the file to the paper |
| `Axioms.lean` | `#print axioms` for every theorem named in this README |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | project configuration |

## Cited results enter as hypotheses

Results that the paper cites are hypotheses of the theorems that use them (Sections 12 and 25 of the file), never
axioms.

| Hypothesis | Cited result | Form in the Lean file |
|---|---|---|
| `FejerRieszHyp` | Fejér–Riesz factorisation (Fejér 1916; Riesz 1916) | |
| `GQSPHypMW` | Theorem 3 of Motlagh and Wiebe (2024) | in their convention: elements of U(2), the signal diag(e^{ix}, 1), no global phase; only the unitarity of their rotations is used, not their parameterisation |
| `GQSPHyp` | derived from `GQSPHypMW` (`gqspHyp_of_MW`), as in the proof of Lemma 3.3 (i) | elements of SU(2), the signal diag(1, e^{ix}) and a constant global phase: diag(e^{ix}, 1) = −(iX) diag(1, e^{ix}) (iX) with iX ∈ SU(2), and each element of U(2) is a phase times an element of SU(2). Every theorem that assumes `GQSPHyp` therefore holds under the cited theorem itself |
| `SardHyp` | Sard's theorem (Sard 1942) | smooth maps from R^n to R^m |
| `HaarNullHyp` | null zero sets of real-analytic functions (Mityagin 2020), applied in charts | on SU(d)^m, the zero set of a polynomial in the real and imaginary parts of the entries that is nonzero at one point is null |

Theorem 3.1 of the paper (Fourier representation) is cited and not formalised. Its serial and ancilla cases are
proved: `gate_model_eq_design`, `ancillaModel_trig`.

## Results of the paper and their Lean theorems

| Result | Lean theorem(s) |
|---|---|
| Lemma 3.2 | `dataJac_eq_design_mul`, `design_gram_eqGrid`, `grid_singular_bounds` |
| Lemma 4.1 (any N, S(x), M) | `coupling_depth` |
| Lemma 4.2 (i) | `gate_tangent_collinear` |
| Lemma 4.2 (ii), Eq. (1) | `gate_phase_locking` |
| Lemma 4.2 (iii), locality | `gate_tangent_local` |
| Lemma 4.2 (iii), degrees of h_j and μ | `gate_tangent_trig`, `gate_envelope_trig` |
| Text after Lemma 4.2: any differentiable parameterisation | `phase_locking` |
| Text after Lemma 4.2: phase of ψ^⊥ | `perp_unit_eq_phase_T`, `perp_phase_invariant` |
| Text after Lemma 4.2: 2·abs(h_j)·abs(μ) bounds the derivative | `envelope_steepest_ascent` |
| Remark 4.3 | `multi_qubit_phase_locking`, `multi_qubit_envelopes`, `multi_qubit_envelope_normSq`, `multi_qubit_envelope_shift`, `multi_qubit_adapted_basis`, `multi_qubit_frame_change`, `tangent_span_frame_invariant` |
| Eq. (2) | `gate_coeffJac_factorisation` |
| Lemma 3.3 (i) | `serial_class_eq`, `ancilla_class_eq`; conversion of the GQSP convention: `gqspHyp_of_MW` |
| Lemma 3.3 (ii) | `serial_generic_full_rank`, `ancilla_generic_full_rank` |
| Proposition 4.4 | `serial_tangent_rank_le`, `serial_tangent_rank_generic`, `ancilla_tangent_rank_generic`, `parallel2_tangent_rank_le`, `parallel2_tangent_rank_generic` |
| Section 4.3 and proof of Proposition 4.4: e_1(x) = U(x)\|1⟩ = −ψ^⊥; dim T = rank H | `T_first_column`; `serial_tangent_rank_eq_rank_H` |
| Corollary 4.5 (i) | `gate_readout_rotation`, `serial_readout_mem_span` |
| abs(μ)² = 1 − f² (Remark 4.3 (ii) for one qubit) | `envelope_normSq`, `gate_envelope_normSq` |
| Corollary 4.5 (ii) | `serial_no_spare_direction` (every choice of gates with full row rank), `serial_readout_in_kernel` ("if", every choice of gates), `serial_no_spare_direction_generic` (almost every choice of gates) |
| Corollary 4.5 (iii) | `serial_no_spare_direction_target`, with `serial_critical_targets_null`, `serial_targets_contain_ball` |
| Lemma B.3 | `stationary_is_least_squares`, `serial_stationary_is_least_squares`, `ancilla_stationary_is_least_squares` |
| Lemma B.1 | `genericity`, with the polynomiality of det(JJᵀ) in the gate entries as a hypothesis (the paper derives it from Lemma 4.1); it is discharged for the serial and the ancilla circuit, the circuits to which the paper applies the lemma, in `serial_generic_full_rank` and `ancilla_generic_full_rank` |
| Lemma B.2 | `stacked_gates_rescale`; Pauli words: `pauli_basis_props` (one qubit), `pauliWord_basis_props` (two qubits) |
| Generality of Definition 3.1: equal outputs, the state is V_M times that of the circuit with blocks W̃, gates in SU(d), bijection | `genModel_reframe`, `genState_reframe`, `reframe_mem_SU`, `reframe_reframe`; `gateModel_eq_genModel`, `ancillaGateModel_eq_genModel`. Not formalised: that J and the tangent span carry over, and the translated forms of Corollary 4.5 (i) and Lemma 4.2 (iii) (Appendix C) |
| Readout rotations: one dimension on one qubit, seven on two | `readout_commutant_one_qubit`; `readout_commutant_two_qubits`, `readoutWord_commute`, `readoutWord_linearIndependent` |
| A readout rotation leaves f unchanged to first order | `readout_rotation_first_order` |
| Directions that leave f unchanged: dimension dim T − rank J | `unchanged_directions_finrank`, `serialUnchanged_finrank`, `ancillaUnchanged_finrank` |
| Serial circuit: only the readout rotation leaves f unchanged | `serialUnchanged_eq_span` |
| Ancilla circuit: Remark 4.3 (ii) for its gates | `ancilla_gate_phase_locking` |
| Ancilla circuit: at least 4E − 2 spare directions | `ancillaRotations_finrank_le`, `ancillaRotations_le_unchanged`, `ancilla_spare_ge`, `ancilla_spare_generic` |
| Parallel circuit: Remark 4.3 (ii) for its gates | `parallel2_gate_phase_locking` |
| Parallel circuit: at least 3E − 2 spare directions | `parallel2_spare_ge`, `parallel2_spare_generic` |

## Conventions of the Lean file

- **Circuits.** Circuits are formalised at the level of gates, as in the paper: L + 1 blocks of a given number of
  gates in SU(2) (serial) or SU(4) (ancilla, parallel), encoding R_X(x), readout Z.
- **L and E.** `L` is the number of encoding layers: the paper's E for the serial and the ancilla circuit, and
  E = 2L for the parallel circuit on two qubits. `tbl` is the number of gates per block.
- **Jacobian.** J (`gateJ`, `ancillaJ`) is the derivative of the vector of Fourier coefficients in Lie-algebra
  coordinates at the current gates. Its columns are derivatives along the curves
  G_i exp(isP) = G_i (cos s · I + i sin s · P), with P² = I for Pauli words.
- **Parameterisation.** In Lemma 4.2 a parameter enters its gate through any differentiable curve of unitaries.
  Lie-algebra coordinates and Euler angles are instances.
- **Time reversal.** Lean's T(z_0, z_1) = (−conj z_1, conj z_0) is −iσ_y 𝒞, with 𝒞 the complex conjugation, and the paper's ψ^⊥ is −Tψ
  (`Tpaper_eq_neg_T`). h_j and μ each change sign with it; the product conj(h_j) μ does not
  (`envelope_product_sign_invariant`).
- **Singular values.** In Lemma 3.2 they are σ_1 and σ_{2E+1}, that is, the extremes of ‖Mᵀy‖ over unit vectors y.
- **Lemma B.2.** It is proved for gates in U(d), for any basis P as stated, and for any gate updates with the stated
  first-order term; exp(−iη g_i · P) is one. The Pauli-word instances are proved for one and two qubits, the cases
  used in the paper.
- **Corollary 4.5 (iii).** A target is identified with its coefficient vector in R^{2E+1}, and the number of gates
  per block is fixed.
- **Spare directions.** The bounds are stated without subtraction, for the ancilla circuit as
  dim(K ∩ R) + 4E ≤ dim K + 2, with K the directions that leave f unchanged to first order and R the readout
  rotations.
- **Parallel circuit.** The project has no coefficient Jacobian for it. A direction leaves f unchanged to first
  order when the corresponding combination of the functions ∂_j f vanishes, and these functions span at most
  2E + 1 dimensions.
