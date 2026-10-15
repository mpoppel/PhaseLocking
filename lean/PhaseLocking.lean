module

public import Mathlib

/-!
# Serial phase-locking in single-qubit data re-uploading circuits

Machine-checked companion to the paper. Part II (Sections 12–24) states and proves the numbered results of Sections 3
and 4 and Appendix B of the paper — Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Remark 4.3, Eq. (2), Proposition 4.4,
Corollary 4.5, Lemma B.1, Lemma B.2 and Lemma B.3 — for circuits of gates, as in the paper, and in
Section 24 the statements the paper makes in running text: the choice of the phase of ψ^⊥ (after Lemma 4.2), the
generality of Definition 3.1, and the readout rotations and spare tangent directions (paragraph "Readout rotations and
spare directions" of Appendix B).
Part I (Sections 1–11) is the machinery it uses. Results the paper cites (Fejér–Riesz, generalised QSP, Sard, null
zero sets on SU(d)^m) are hypotheses of the theorems that use them (Section 12), never axioms. The README maps each
result to its Lean theorems; Appendix C of the paper says what is and what is not formalised.

In this file `L` is the number of encoding layers (the paper's `E` for the serial and the ancilla circuit; `E = 2L`
for the parallel circuit on two qubits) and `tbl` the number of gates per block.

Part I
* 1   algebraic core: `perp_eq_smul_T`, `envelope_identity`
* 2   sign convention of the time reversal: `Tpaper_eq_neg_T`, `envelope_product_sign_invariant`
* 3   gauge: `T_mulVec_SU2`, `gauge_invariance`
* 4   calculus on curves: `tangent_of_normalised`, `expval_hasDerivAt`, `phase_locking` (any parameterisation)
* 5   Fourier form of the envelope product: `envelope_expansion`
* 6   several qubits (Remark 4.3(i), (ii)): `multi_qubit_envelopes`, `multi_qubit_phase_locking`
* 7   degree bookkeeping: `serialState_expansion`, `pairing_integer_frequencies`
* 8–11 the serial circuit in Euler-angle coordinates (used for the full-rank witness), derivatives of serial states,
       analyticity, real coordinates and the envelope matrix A_μ, `rot_surjective`

Part II
* 12  cited results as hypotheses: `FejerRieszHyp`, `GQSPHyp`, `SardHyp`, `HaarNullHyp`
* 13  Fourier coefficients, design matrix, grid Gram matrix
* 14  Lemma 4.1 (polynomial structure): `coupling_depth`
* 15  gate-level serial circuit; Lemma 4.2: `gate_tangent_collinear` (i), `gate_phase_locking` (ii),
       `gate_tangent_local`, `gate_tangent_trig`, `gate_envelope_trig` (iii); Definition 3.2: `gateJ`;
       Eq. (2): `gate_coeffJac_factorisation`
* 16  Lemma 3.2: `dataJac_eq_design_mul`, `design_gram_eqGrid`, `grid_singular_bounds`;
       Lemma B.3: `stationary_is_least_squares`, `serial_stationary_is_least_squares`
* 17  ancilla circuit: `ancillaJ`, `ancilla_stationary_is_least_squares`
* 18  Lemma 3.3(i): `serial_class_eq`, `ancilla_class_eq`
* 19  Lemma B.1: `genericity`; Lemma 3.3(ii): `serial_generic_full_rank`, `ancilla_generic_full_rank`
* 20  Lemma B.2: `stacked_gates_rescale`, with `pauli_basis_props`, `pauliWord_basis_props`
* 21  Proposition 4.4(i), (ii): `serial_tangent_rank_le`, `serial_tangent_rank_generic`, `ancilla_tangent_rank_generic`
       (general witness lemma `tangent_rank_generic_of_witness`)
* 22  Proposition 4.4(iii): `parallel2_tangent_rank_le`, `parallel2_tangent_rank_generic`
* 23  Remark 4.3(ii), (iii) (norm, adapted basis, change of basis): `multi_qubit_envelope_normSq`,
       `multi_qubit_envelope_shift`, `multi_qubit_adapted_basis`, `multi_qubit_frame_change`,
       `tangent_span_frame_invariant`; for one qubit `gate_envelope_normSq`;
       Corollary 4.5(i): `gate_readout_rotation`, `serial_readout_mem_span`;
       Corollary 4.5(ii): `serial_readout_in_kernel` ("if", every choice of gates),
       `serial_no_spare_direction_generic` (almost every choice of gates)
* 24  Corollary 4.5(ii) at every choice of gates with full row rank: `serial_no_spare_direction`,
       `serial_tangent_rank_of_full_rank`; Corollary 4.5(iii): `serial_critical_targets_null`,
       `serial_no_spare_direction_target`, `serial_targets_contain_ball`;
       text of Sections 4.2 and 4.3: `perp_unit_eq_phase_T`, `perp_phase_invariant`, `envelope_steepest_ascent`,
       `T_first_column`, `serial_tangent_rank_eq_rank_H`;
       generality of Definition 3.1: `genModel_reframe`, `reframe_mem_SU`, `reframe_reframe`,
       `gateModel_eq_genModel`, `ancillaGateModel_eq_genModel`;
       readout rotations and spare directions: `readout_commutant_one_qubit`, `readout_commutant_two_qubits`,
       `readoutWord_commute`, `readoutWord_linearIndependent`, `readout_rotation_first_order`,
       `serialUnchanged_finrank`, `serialUnchanged_eq_span`, `ancilla_gate_phase_locking`,
       `ancillaUnchanged_finrank`, `ancilla_readout_rotations_eq`, `ancillaRotations_finrank_le`,
       `ancillaRotations_le_unchanged`, `ancilla_spare_ge`, `ancilla_spare_generic`;
       parallel circuit (optional part): `parallel2_gate_phase_locking`, `parallel2Unchanged_finrank_ge`,
       `parallel2_spare_ge`, `parallel2_spare_generic`

Notation: `ip u v = conj(u₀) v₀ + conj(u₁) v₁`; `T (z₀, z₁) = (−conj z₁, conj z₀)`, equal to −iσ_y K. The paper's
`ψ^⊥ = (conj ψ₁, −conj ψ₀)` is `−T ψ` (`Tpaper_eq_neg_T`); `h_j` and `μ` each change sign with it, the vector
`h_j ψ^⊥` and the product `conj(h_j) μ` do not (`envelope_product_sign_invariant`, `perp_phase_invariant`).
-/

@[expose] public section

open Matrix

set_option autoImplicit false

noncomputable section

/-! ## 1. Algebraic core of phase-locking -/

/-- Hermitian inner product on ℂ², conjugate-linear in the first slot. -/
def ip (u v : Fin 2 → ℂ) : ℂ := (starRingEnd ℂ) (u 0) * v 0 + (starRingEnd ℂ) (u 1) * v 1

/-- Time reversal `T (z₀, z₁) = (-conj z₁, conj z₀)`. -/
def T (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![-(starRingEnd ℂ) (v 1), (starRingEnd ℂ) (v 0)]

/-- ψ^⊥ is one-dimensional and spanned by Tψ. -/
theorem perp_eq_smul_T (ψ v : Fin 2 → ℂ) (hψ : ip ψ ψ = 1) (hv : ip ψ v = 0) :
    v = ip (T ψ) v • T ψ := by
  simp only [ip] at hψ hv
  funext i
  fin_cases i
  · simp [ip, T]
    linear_combination -(v 0) * hψ + ψ 0 * hv
  · simp [ip, T]
    linear_combination -(v 1) * hψ + ψ 1 * hv

theorem ip_herm_im {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᴴ = M) (ψ : Fin 2 → ℂ) :
    (ip ψ (M *ᵥ ψ)).im = 0 := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h11 := congrFun (congrFun hM 1) 1
  simp [conjTranspose_apply, Complex.ext_iff] at h00 h01 h11
  simp [ip, mulVec, dotProduct, Fin.sum_univ_two]
  have h00' : (M 0 0).im = 0 := by linarith
  have h11' : (M 1 1).im = 0 := by linarith
  rw [← h01.1, ← h01.2, h00', h11']
  ring

/-- Phase-locking / shared envelope: for a unit ψ, a tangent vector dψ of the normalised state and Hermitian M,
    2 Re⟨dψ, Mψ⟩ = 2 Re[conj(⟨Tψ, dψ⟩) · ⟨Tψ, Mψ⟩]. -/
theorem envelope_identity (ψ dψ : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hψ : ip ψ ψ = 1) (htan : (ip ψ dψ).re = 0) (hM : Mᴴ = M) :
    2 * (ip dψ (M *ᵥ ψ)).re =
      2 * ((starRingEnd ℂ) (ip (T ψ) dψ) * ip (T ψ) (M *ᵥ ψ)).re := by
  set a := ip ψ dψ with ha
  set b := ip (T ψ) dψ with hb
  have hperp : ip ψ (dψ - a • ψ) = 0 := by
    have : ip ψ (dψ - a • ψ) = a - a * ip ψ ψ := by
      simp [ip, a]; ring
    rw [this, hψ]; ring
  have hdec := perp_eq_smul_T ψ _ hψ hperp
  have hcoef : ip (T ψ) (dψ - a • ψ) = b := by
    simp [ip, T, b]; ring
  rw [hcoef] at hdec
  have hd : dψ = a • ψ + b • T ψ := by
    rw [← hdec]; abel
  have hexp : ip dψ (M *ᵥ ψ) = (starRingEnd ℂ) a * ip ψ (M *ᵥ ψ) +
      (starRingEnd ℂ) b * ip (T ψ) (M *ᵥ ψ) := by
    conv_lhs => rw [hd]
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  rw [hexp, Complex.add_re]
  have hr := ip_herm_im hM ψ
  have : ((starRingEnd ℂ) a * ip ψ (M *ᵥ ψ)).re = 0 := by
    simp [Complex.mul_re, htan, hr]
  rw [this]; ring

/-! ## 2. Sign convention of the time reversal -/

/-- The paper's anti-unitary time reversal `T = iσ_y K`: `(z₀, z₁) ↦ (conj z₁, −conj z₀)`. -/
def Tpaper (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![(starRingEnd ℂ) (v 1), -(starRingEnd ℂ) (v 0)]

theorem Tpaper_eq_neg_T (v : Fin 2 → ℂ) : Tpaper v = -T v := by
  funext i
  fin_cases i <;> simp [Tpaper, T]

/-- The envelope product is independent of the sign convention. -/
theorem envelope_product_sign_invariant (ψ dψ w : Fin 2 → ℂ) :
    (starRingEnd ℂ) (ip (Tpaper ψ) dψ) * ip (Tpaper ψ) w =
      (starRingEnd ℂ) (ip (T ψ) dψ) * ip (T ψ) w := by
  rw [Tpaper_eq_neg_T]
  simp only [ip, Pi.neg_apply, map_neg, map_add, map_mul]
  ring

/-! ## 3. Gauge: T commutes with SU(2); h_j does not see the downstream circuit -/

theorem T_mulVec_SU2 (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (v : Fin 2 → ℂ) : T (D *ᵥ v) = D *ᵥ T v := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff'] at hD
  obtain ⟨hU, hdet⟩ := hD
  have hadj : D * D.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hs : star D = D.adjugate := by
    calc star D = star D * (D * D.adjugate) := by rw [hadj, mul_one]
      _ = (star D * D) * D.adjugate := by rw [mul_assoc]
      _ = D.adjugate := by rw [hU, one_mul]
  rw [Matrix.adjugate_fin_two] at hs
  have e1 := congrFun (congrFun hs 0) 0
  have e2 := congrFun (congrFun hs 0) 1
  have e3 := congrFun (congrFun hs 1) 0
  have e4 := congrFun (congrFun hs 1) 1
  simp [Matrix.star_apply] at e1 e2 e3 e4
  funext i
  fin_cases i
  · simp [T, mulVec, dotProduct, Fin.sum_univ_two]
    rw [e2, e4]; ring
  · simp [T, mulVec, dotProduct, Fin.sum_univ_two]
    rw [e1, e3]; ring

theorem ip_unitary (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : D ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u v : Fin 2 → ℂ) : ip (D *ᵥ u) (D *ᵥ v) = ip u v := by
  rw [Matrix.mem_unitaryGroup_iff'] at hD
  have e00 := congrFun (congrFun hD 0) 0
  have e01 := congrFun (congrFun hD 0) 1
  have e10 := congrFun (congrFun hD 1) 0
  have e11 := congrFun (congrFun hD 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e01 e10 e11
  simp [ip, mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (starRingEnd ℂ (u 0) * v 0) * e00 + (starRingEnd ℂ (u 0) * v 1) * e01 +
    (starRingEnd ℂ (u 1) * v 0) * e10 + (starRingEnd ℂ (u 1) * v 1) * e11

/-- Gauge invariance: if ψ = D φ with D ∈ SU(2) the downstream circuit, then
    h = ⟨Tψ, D w⟩ = ⟨Tφ, w⟩ is computed from the sub-circuit up to the current block alone. -/
theorem gauge_invariance (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (φ w : Fin 2 → ℂ) : ip (T (D *ᵥ φ)) (D *ᵥ w) = ip (T φ) w := by
  rw [T_mulVec_SU2 D hD, ip_unitary D hD.1]

/-! ## 4. Calculus: from a differentiable normalised state to the envelope form -/

theorem ip_conj_symm (u v : Fin 2 → ℂ) : ip v u = (starRingEnd ℂ) (ip u v) := by
  simp [ip]; ring

theorem ip_herm_swap {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᴴ = M) (u v : Fin 2 → ℂ) :
    ip u (M *ᵥ v) = (starRingEnd ℂ) (ip v (M *ᵥ u)) := by
  have e : ∀ i j, (starRingEnd ℂ) (M j i) = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [conjTranspose_apply] using this
  simp only [ip, mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj]
  rw [e 0 0, e 0 1, e 1 0, e 1 1]; ring

theorem hasDerivAt_ip (u v : ℝ → Fin 2 → ℂ) (du dv : Fin 2 → ℂ) (t : ℝ)
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => ip (u s) (v s)) (ip du (v t) + ip (u t) dv) t := by
  have hu' := fun i => hasDerivAt_pi.1 hu i
  have hv' := fun i => hasDerivAt_pi.1 hv i
  have hc : ∀ i, HasDerivAt (fun s => (starRingEnd ℂ) (u s i)) ((starRingEnd ℂ) (du i)) t :=
    fun i => (hu' i).star
  have := ((hc 0).mul (hv' 0)).add ((hc 1).mul (hv' 1))
  convert this using 1
  simp only [ip]; ring

theorem hasDerivAt_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : ℝ → Fin 2 → ℂ) (dψ : Fin 2 → ℂ)
    (t : ℝ) (hd : HasDerivAt ψ dψ t) : HasDerivAt (fun s => M *ᵥ ψ s) (M *ᵥ dψ) t := by
  apply hasDerivAt_pi.2
  intro i
  have h0 := hasDerivAt_pi.1 hd 0
  have h1 := hasDerivAt_pi.1 hd 1
  simpa [mulVec, dotProduct, Fin.sum_univ_two] using
    (h0.const_mul (M i 0)).add (h1.const_mul (M i 1))

/-- Normalisation implies the tangent condition `Re⟨ψ, ψ'⟩ = 0`. -/
theorem tangent_of_normalised (ψ : ℝ → Fin 2 → ℂ) (dψ : Fin 2 → ℂ) (t : ℝ)
    (hnorm : ∀ s, ip (ψ s) (ψ s) = 1) (hd : HasDerivAt ψ dψ t) :
    (ip (ψ t) dψ).re = 0 := by
  have h1 := hasDerivAt_ip ψ ψ dψ dψ t hd hd
  have h2 : HasDerivAt (fun s => ip (ψ s) (ψ s)) 0 t := by
    simp only [hnorm]; exact hasDerivAt_const _ _
  have h3 := congrArg Complex.re (h1.unique h2)
  rw [ip_conj_symm (ψ t) dψ] at h3
  simp at h3
  linarith

/-- Derivative of the expectation value `⟨ψ|M|ψ⟩` for Hermitian `M`. -/
theorem expval_hasDerivAt (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᴴ = M)
    (ψ : ℝ → Fin 2 → ℂ) (dψ : Fin 2 → ℂ) (t : ℝ) (hd : HasDerivAt ψ dψ t) :
    HasDerivAt (fun s => (ip (ψ s) (M *ᵥ ψ s)).re) (2 * (ip dψ (M *ᵥ ψ t)).re) t := by
  have h := hasDerivAt_ip ψ (fun s => M *ᵥ ψ s) dψ (M *ᵥ dψ) t hd (hasDerivAt_mulVec M ψ dψ t hd)
  have h' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  convert h' using 1
  simp only [Complex.reCLM_apply, Complex.add_re]
  rw [ip_herm_swap hM (ψ t) dψ, Complex.conj_re]
  ring

/-- Serial phase-locking, calculus form. For P one-parameter variations γ_j of a normalised single-qubit
    state through the same point ψ₀ (e.g. γ_j(s) = ψ(θ + s e_j)), every derivative of ⟨ψ|M|ψ⟩ factors
    through one envelope μ: ∂_j f = 2 Re[conj(⟨Tψ₀, ∂_jψ⟩) μ]. -/
theorem phase_locking {P : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Mᴴ = M)
    (γ : Fin P → ℝ → Fin 2 → ℂ) (ψ₀ : Fin 2 → ℂ) (dψ : Fin P → Fin 2 → ℂ)
    (h0 : ∀ j, γ j 0 = ψ₀) (hnorm : ∀ j s, ip (γ j s) (γ j s) = 1)
    (hd : ∀ j, HasDerivAt (γ j) (dψ j) 0) :
    ∃ μ : ℂ, ∀ j, HasDerivAt (fun s => (ip (γ j s) (M *ᵥ γ j s)).re)
      (2 * ((starRingEnd ℂ) (ip (T ψ₀) (dψ j)) * μ).re) 0 := by
  refine ⟨ip (T ψ₀) (M *ᵥ ψ₀), fun j => ?_⟩
  have hψ : ip ψ₀ ψ₀ = 1 := by rw [← h0 j]; exact hnorm j 0
  have htan : (ip ψ₀ (dψ j)).re = 0 := by
    rw [← h0 j]; exact tangent_of_normalised (γ j) (dψ j) 0 (hnorm j) (hd j)
  have h := expval_hasDerivAt M hM (γ j) (dψ j) 0 (hd j)
  rw [h0 j, envelope_identity ψ₀ (dψ j) M hψ htan hM] at h
  exact h

/-! ## 5. Fourier form of the envelope product -/

/-- Trigonometric polynomial with coefficients `a k`, `|k| ≤ L`. -/
def trig (L : ℕ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(L : ℤ)) L, a k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))

/-- Fourier coefficients of 2 Re[conj(h) μ] for h = trig L a, μ = trig L b:
    c_m = Σ_k (conj(a_k) b_{k+m} + conj(b_k) a_{k+m}). -/
def envCoeff (L : ℕ) (a b : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(L : ℤ)) L,
    ((starRingEnd ℂ) (a k) * b (k + m) + (starRingEnd ℂ) (b k) * a (k + m))

theorem conj_trig_mul_trig (L : ℕ) (a b : ℤ → ℂ) (x : ℝ) :
    (starRingEnd ℂ) (trig L a x) * trig L b x =
      ∑ k ∈ Finset.Icc (-(L : ℤ)) L, ∑ l ∈ Finset.Icc (-(L : ℤ)) L,
        (starRingEnd ℂ) (a k) * b l * Complex.exp (Complex.I * ((l - k : ℤ) : ℂ) * (x : ℂ)) := by
  simp only [trig, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.exp_conj]
  calc _ = (starRingEnd ℂ) (a k) * b l * (Complex.exp ((starRingEnd ℂ) (Complex.I * k * x)) *
        Complex.exp (Complex.I * l * x)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      simp
      ring

theorem sum_shift_reindex (L : ℕ) (F : ℤ → ℤ → ℂ)
    (hF : ∀ k l, l ∉ Finset.Icc (-(L : ℤ)) L → F k l = 0) (x : ℝ) :
    ∑ m ∈ Finset.Icc (-(2 * L : ℤ)) (2 * L), ∑ k ∈ Finset.Icc (-(L : ℤ)) L,
      F k (k + m) * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) =
    ∑ k ∈ Finset.Icc (-(L : ℤ)) L, ∑ l ∈ Finset.Icc (-(L : ℤ)) L,
      F k l * Complex.exp (Complex.I * ((l - k : ℤ) : ℂ) * (x : ℂ)) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  set g : ℤ → ℂ := fun l => F k l * Complex.exp (Complex.I * ((l - k : ℤ) : ℂ) * (x : ℂ)) with hg
  have h1 : ∀ m : ℤ, F k (k + m) * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) = g (k + m) := by
    intro m; simp only [hg]; congr 3; push_cast; ring
  simp_rw [h1]
  rw [show (∑ m ∈ Finset.Icc (-(2 * L : ℤ)) (2 * L), g (k + m)) =
      ∑ l ∈ Finset.Icc (k + -(2 * L : ℤ)) (k + 2 * L), g l by
    rw [← Finset.map_add_left_Icc, Finset.sum_map]; rfl]
  symm
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_Icc] at hl hk ⊢
    omega
  · intro l _ hl
    rw [hF k l hl, zero_mul]

theorem envelope_expansion (L : ℕ) (a b : ℤ → ℂ)
    (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0)
    (hb : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0) (x : ℝ) :
    ((2 * ((starRingEnd ℂ) (trig L a x) * trig L b x).re : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc (-(2 * L : ℤ)) (2 * L),
        envCoeff L a b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) := by
  have hz : (((2 * ((starRingEnd ℂ) (trig L a x) * trig L b x).re : ℝ)) : ℂ) =
      (starRingEnd ℂ) (trig L a x) * trig L b x + (starRingEnd ℂ) (trig L b x) * trig L a x := by
    rw [← Complex.add_conj]
    simp only [map_mul, Complex.conj_conj]
    ring
  have e1 := sum_shift_reindex L (fun k l => (starRingEnd ℂ) (a k) * b l)
    (fun k l hl => by simp only; rw [hb l hl, mul_zero]) x
  have e2 := sum_shift_reindex L (fun k l => (starRingEnd ℂ) (b k) * a l)
    (fun k l hl => by simp only; rw [ha l hl, mul_zero]) x
  simp only at e1 e2
  rw [hz, conj_trig_mul_trig, conj_trig_mul_trig, ← e1, ← e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [envCoeff, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## 6. Several qubits: several envelopes (Remark 4.3) -/

open scoped InnerProductSpace in
/-- For any pure state `b 0` in ℂ^{d+1}, an orthonormal basis `b` extending it, a tangent vector dψ and a
    self-adjoint M: ∂f = 2 Re Σ_{r=1}^{d} conj(⟨b r, dψ⟩) ⟨b r, M b 0⟩ — up to d = 2^N − 1 envelopes.
    The serial case is d = 1. -/
theorem multi_qubit_envelopes {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℂ (EuclideanSpace ℂ (Fin (d + 1))))
    (M : EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1))) (hM : M.IsSymmetric)
    (dψ : EuclideanSpace ℂ (Fin (d + 1))) (htan : (⟪b 0, dψ⟫_ℂ).re = 0) :
    2 * (⟪dψ, M (b 0)⟫_ℂ).re =
      2 * (∑ r : Fin d, (starRingEnd ℂ) ⟪b r.succ, dψ⟫_ℂ * ⟪b r.succ, M (b 0)⟫_ℂ).re := by
  have hexp : ⟪dψ, M (b 0)⟫_ℂ = ∑ r, (starRingEnd ℂ) ⟪b r, dψ⟫_ℂ * ⟪b r, M (b 0)⟫_ℂ := by
    rw [← b.sum_inner_mul_inner dψ (M (b 0))]
    simp [inner_conj_symm]
  rw [hexp, Fin.sum_univ_succ, Complex.add_re]
  have hreal : (⟪b 0, M (b 0)⟫_ℂ).im = 0 := by
    have h := hM (b 0) (b 0)
    rw [← inner_conj_symm] at h
    exact Complex.conj_eq_iff_im.mp h
  have h0 : ((starRingEnd ℂ) ⟪b 0, dψ⟫_ℂ * ⟪b 0, M (b 0)⟫_ℂ).re = 0 := by
    rw [Complex.mul_re, Complex.conj_re, htan, hreal]; ring
  rw [h0, zero_add]

open scoped InnerProductSpace in
/-- **Remark 4.3.** For a differentiable curve of pure states `ψ` in ℂ^{d+1} (any parameterisation), a self-adjoint
    readout `M` and an orthonormal basis `b` with `b 0 = ψ 0`, the derivative of `f = ⟨ψ, Mψ⟩` is
    `2 Re Σ_{r=1}^{d} conj(h_r) μ_r` with `h_r = ⟨b r, ∂ψ⟩` and `μ_r = ⟨b r, M ψ⟩`: up to `d = 2^N − 1` envelopes. -/
theorem multi_qubit_phase_locking {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℂ (EuclideanSpace ℂ (Fin (d + 1))))
    (M : EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1))) (hM : M.IsSymmetric)
    (ψ : ℝ → EuclideanSpace ℂ (Fin (d + 1))) (dψ : EuclideanSpace ℂ (Fin (d + 1)))
    (hψ : HasDerivAt ψ dψ 0) (hnorm : ∀ s, ‖ψ s‖ = 1) (hb : b 0 = ψ 0) :
    HasDerivAt (fun s => (⟪ψ s, M (ψ s)⟫_ℂ).re)
      (2 * (∑ r : Fin d, (starRingEnd ℂ) ⟪b r.succ, dψ⟫_ℂ * ⟪b r.succ, M (b 0)⟫_ℂ).re) 0 := by
  set Mc : EuclideanSpace ℂ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (d + 1)) :=
    (LinearMap.toContinuousLinearMap M).restrictScalars ℝ
  have hMψ : HasDerivAt (fun s => M (ψ s)) (M dψ) 0 := by
    have := Mc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψ
    simpa [Mc] using this
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hψ.inner ℂ hMψ)
  have hn2 : HasDerivAt (fun s => (⟪ψ s, ψ s⟫_ℂ).re) (⟪ψ 0, dψ⟫_ℂ + ⟪dψ, ψ 0⟫_ℂ).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hψ.inner ℂ hψ)
  have hconst : (fun s => (⟪ψ s, ψ s⟫_ℂ).re) = fun _ => (1 : ℝ) := by
    funext s; rw [inner_self_eq_norm_sq_to_K, hnorm s]; simp
  rw [hconst] at hn2
  have h0 := hn2.unique (hasDerivAt_const _ _)
  have htan : (⟪b 0, dψ⟫_ℂ).re = 0 := by
    rw [hb]; rw [Complex.add_re, ← inner_conj_symm dψ (ψ 0), Complex.conj_re] at h0; linarith
  rw [← multi_qubit_envelopes b M hM dψ htan, hb]
  convert hre using 1
  simp only [Complex.reCLM_apply, Complex.add_re]
  rw [← hM (ψ 0) dψ, ← inner_conj_symm dψ (M (ψ 0)), Complex.conj_re]
  ring

/-! ## 7. Degree bookkeeping for the serial circuit -/

/-- `R_X(x)` as a 2×2 matrix. -/
def RXm (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos (x / 2), -Complex.I * Complex.sin (x / 2);
     -Complex.I * Complex.sin (x / 2), Complex.cos (x / 2)]

/-- Serial state after `L` encoding layers: `V_L R_X(x) V_{L-1} ⋯ R_X(x) V_0 e₀`. -/
def serialState : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → Fin 2 → ℂ
  | 0, V, _ => V 0 *ᵥ ![1, 0]
  | L + 1, V, x => V (Fin.last (L + 1)) *ᵥ (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x)

theorem sum_Icc_shift (L : ℕ) (s : ℤ) (hs : -1 ≤ s ∧ s ≤ 1) (f g : ℤ → ℂ)
    (hf : ∀ j, j ∉ Finset.Icc (-(L : ℤ)) L → f j = 0) :
    ∑ k ∈ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ), f (k - s) * g k =
      ∑ j ∈ Finset.Icc (-(L : ℤ)) L, f j * g (j + s) := by
  rw [show Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ) =
      (Finset.Icc (-((L + 1 : ℕ) : ℤ) - s) ((L + 1 : ℕ) - s)).map (addRightEmbedding s) by
    rw [Finset.map_add_right_Icc]; simp]
  rw [Finset.sum_map]
  simp only [addRightEmbedding_apply, add_sub_cancel_right]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    push_cast
    omega
  · intro j _ hj
    rw [hf j hj, zero_mul]

/-- Each amplitude is a half-integer trigonometric polynomial Σ_{|k|≤L, k ≡ L mod 2} c_k e^{ikx/2}. -/
theorem serialState_expansion (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ c : Fin 2 → ℤ → ℂ,
      (∀ i k, c i k ≠ 0 → k ∈ Finset.Icc (-(L : ℤ)) L ∧ Even (k + L)) ∧
      ∀ x i, serialState L V x i =
        ∑ k ∈ Finset.Icc (-(L : ℤ)) L, c i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) := by
  induction L with
  | zero =>
    refine ⟨fun i k => if k = 0 then V 0 i 0 else 0, ?_, ?_⟩
    · intro i k h
      by_cases hk : k = 0
      · subst hk; simp
      · simp [hk] at h
    · intro x i
      simp [serialState, mulVec, dotProduct, Fin.sum_univ_two]
  | succ L ih =>
    obtain ⟨c', hsupp', hrep'⟩ := ih (fun i => V (Fin.castSucc i))
    set Vl := V (Fin.last (L + 1)) with hVl
    set d : ℤ → ℂ := fun k => c' 0 k - c' 1 k with hd
    set e : ℤ → ℂ := fun k => c' 0 k + c' 1 k with he
    have hc'0 : ∀ i k, ¬ (k ∈ Finset.Icc (-(L : ℤ)) L ∧ Even (k + L)) → c' i k = 0 := by
      intro i k hk
      by_contra h
      exact hk (hsupp' i k h)
    refine ⟨fun i k => (Vl i 0 - Vl i 1) / 2 * d (k - 1) + (Vl i 0 + Vl i 1) / 2 * e (k + 1),
      ?_, ?_⟩
    · intro i k h
      by_contra hcon
      apply h
      have h1 : ¬ (k - 1 ∈ Finset.Icc (-(L : ℤ)) L ∧ Even (k - 1 + L)) := by
        intro h2; apply hcon
        simp only [Finset.mem_Icc, Int.even_iff] at h2 ⊢
        push_cast
        omega
      have h2 : ¬ (k + 1 ∈ Finset.Icc (-(L : ℤ)) L ∧ Even (k + 1 + L)) := by
        intro h2; apply hcon
        simp only [Finset.mem_Icc, Int.even_iff] at h2 ⊢
        push_cast
        omega
      simp only [hd, he, hc'0 0 _ h1, hc'0 1 _ h1, hc'0 0 _ h2, hc'0 1 _ h2]
      ring
    · intro x i
      set E : ℤ → ℂ := fun k => Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) with hE
      have hEadd : ∀ j s : ℤ, E (j + s) = E j * E s := by
        intro j s
        simp only [hE, ← Complex.exp_add]
        congr 1; push_cast; ring
      have hcos : Complex.cos ((x : ℂ) / 2) = (E 1 + E (-1)) / 2 := by
        simp only [hE, Complex.cos]
        congr 2 <;> congr 1 <;> push_cast <;> ring
      have hsin : -Complex.I * Complex.sin ((x : ℂ) / 2) = (E (-1) - E 1) / 2 := by
        simp only [hE, Complex.sin]
        rw [show (Complex.I * ((-1 : ℤ) : ℂ) * (x : ℂ) / 2) = -((x : ℂ) / 2) * Complex.I by
              push_cast; ring,
            show (Complex.I * ((1 : ℤ) : ℂ) * (x : ℂ) / 2) = ((x : ℂ) / 2) * Complex.I by
              push_cast; ring]
        ring_nf
        rw [Complex.I_sq]
        ring
      have hS : ∀ j, serialState L (fun i => V (Fin.castSucc i)) x j =
          ∑ k ∈ Finset.Icc (-(L : ℤ)) L, c' j k * E k := fun j => hrep' x j
      have hdz : ∀ j, j ∉ Finset.Icc (-(L : ℤ)) L → d j = 0 := by
        intro j hj
        simp only [hd, hc'0 0 j (fun h => hj h.1), hc'0 1 j (fun h => hj h.1), sub_zero]
      have hez : ∀ j, j ∉ Finset.Icc (-(L : ℤ)) L → e j = 0 := by
        intro j hj
        simp only [he, hc'0 0 j (fun h => hj h.1), hc'0 1 j (fun h => hj h.1), add_zero]
      have hsplit : ∑ k ∈ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ),
          ((Vl i 0 - Vl i 1) / 2 * d (k - 1) + (Vl i 0 + Vl i 1) / 2 * e (k + 1)) * E k =
          (Vl i 0 - Vl i 1) / 2 * ∑ k ∈ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ),
              d (k - 1) * E k +
          (Vl i 0 + Vl i 1) / 2 * ∑ k ∈ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ),
              e (k - (-1)) * E k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_neg_eq_add]; ring
      have hRHS := hsplit
      rw [sum_Icc_shift L 1 (by norm_num) d E hdz, sum_Icc_shift L (-1) (by norm_num) e E hez]
        at hRHS
      simp only [hEadd] at hRHS
      have hd' : ∑ j ∈ Finset.Icc (-(L : ℤ)) L, d j * (E j * E 1) =
          E 1 * (serialState L (fun i => V (Fin.castSucc i)) x 0 -
            serialState L (fun i => V (Fin.castSucc i)) x 1) := by
        rw [hS, hS, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hd]; ring
      have he' : ∑ j ∈ Finset.Icc (-(L : ℤ)) L, e j * (E j * E (-1)) =
          E (-1) * (serialState L (fun i => V (Fin.castSucc i)) x 0 +
            serialState L (fun i => V (Fin.castSucc i)) x 1) := by
        rw [hS, hS, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [he]; ring
      rw [hd', he'] at hRHS
      show _ = ∑ k ∈ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ),
          ((Vl i 0 - Vl i 1) / 2 * d (k - 1) + (Vl i 0 + Vl i 1) / 2 * e (k + 1)) * E k
      rw [hRHS]
      simp only [serialState, mulVec, dotProduct, Fin.sum_univ_two, RXm, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      have hsin' : Complex.sin ((x : ℂ) / 2) = Complex.I * ((E (-1) - E 1) / 2) := by
        linear_combination Complex.I * hsin + Complex.sin ((x : ℂ) / 2) * Complex.I_sq
      rw [← hVl, hcos, hsin']
      ring_nf
      simp only [Complex.I_sq]
      ring

/-- The bilinear pairing ⟨Tu, G w⟩ of two parity-ℓ half-integer expansions of degree ≤ ℓ is an
    integer-frequency trigonometric polynomial of degree ≤ ℓ. Applied with u = w = serial state (G = M) this
    gives μ ∈ 𝒯_L; with the state after block j (G = (∂V_j)V_j⁻¹) it gives the degree bound on h_j. -/
theorem pairing_integer_frequencies (ℓ : ℕ) (cu cw : Fin 2 → ℤ → ℂ)
    (hu : ∀ i k, cu i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ))
    (hw : ∀ i k, cw i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ))
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(ℓ : ℤ)) ℓ → a k = 0) ∧ ∀ x : ℝ,
      ip (T (fun i => ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ, cu i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2)))
         (G *ᵥ fun i => ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ, cw i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2))
        = trig ℓ a x := by
  classical
  set Iℓ := Finset.Icc (-(ℓ : ℤ)) ℓ with hIℓ
  set C : ℤ → ℤ → ℂ := fun k l => G 1 0 * cu 0 k * cw 0 l + G 1 1 * cu 0 k * cw 1 l +
      (-G 0 0) * cu 1 k * cw 0 l + (-G 0 1) * cu 1 k * cw 1 l with hC
  have hu0 : ∀ i k, ¬ (k ∈ Iℓ ∧ Even (k + ℓ)) → cu i k = 0 := fun i k hk => by
    by_contra h; exact hk (hu i k h)
  have hw0 : ∀ i k, ¬ (k ∈ Iℓ ∧ Even (k + ℓ)) → cw i k = 0 := fun i k hk => by
    by_contra h; exact hk (hw i k h)
  have hCsupp : ∀ k l, C k l ≠ 0 → (k ∈ Iℓ ∧ Even (k + ℓ)) ∧ (l ∈ Iℓ ∧ Even (l + ℓ)) := by
    intro k l h
    by_contra hcon
    apply h
    rcases not_and_or.1 hcon with h1 | h1
    · simp only [hC, hu0 0 k h1, hu0 1 k h1]; ring
    · simp only [hC, hw0 0 l h1, hw0 1 l h1]; ring
  refine ⟨fun n => ∑ k ∈ Iℓ, ∑ l ∈ Iℓ, if k + l = 2 * n then C k l else 0, ?_, ?_⟩
  · intro n hn
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    rw [if_neg]
    intro h
    apply hn
    simp only [hIℓ, Finset.mem_Icc] at hk hl ⊢
    omega
  · intro x
    set E : ℤ → ℂ := fun k => Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) with hE
    have hT : ∀ u v : Fin 2 → ℂ, ip (T u) (G *ᵥ v) = G 1 0 * u 0 * v 0 + G 1 1 * u 0 * v 1 +
        (-G 0 0) * u 1 * v 0 + (-G 0 1) * u 1 * v 1 := by
      intro u v; simp [ip, T, mulVec, dotProduct, Fin.sum_univ_two]; ring
    have aux : ∀ (g : ℂ) (f h : ℤ → ℂ), g * (∑ k ∈ Iℓ, f k * E k) * (∑ l ∈ Iℓ, h l * E l) =
        ∑ k ∈ Iℓ, ∑ l ∈ Iℓ, g * f k * h l * (E k * E l) := by
      intro g f h
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hL : ip (T (fun i => ∑ k ∈ Iℓ, cu i k * E k)) (G *ᵥ fun i => ∑ k ∈ Iℓ, cw i k * E k) =
        ∑ k ∈ Iℓ, ∑ l ∈ Iℓ, C k l * (E k * E l) := by
      rw [hT, aux, aux, aux, aux]
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [hC]; ring
    show ip (T (fun i => ∑ k ∈ Iℓ, cu i k * E k)) (G *ᵥ fun i => ∑ k ∈ Iℓ, cw i k * E k) = _
    rw [hL, trig]
    simp only [Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl => ?_
    by_cases hc : C k l = 0
    · simp [hc]
    obtain ⟨⟨-, hk2⟩, ⟨-, hl2⟩⟩ := hCsupp k l hc
    rw [Int.even_iff] at hk2 hl2
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, k + l = 2 * n0 := ⟨(k + l) / 2, by omega⟩
    have hn0mem : n0 ∈ Iℓ := by
      simp only [hIℓ, Finset.mem_Icc] at hk hl ⊢
      omega
    rw [Finset.sum_eq_single n0]
    · rw [if_pos hn0]
      congr 1
      simp only [hE, ← Complex.exp_add]
      congr 1
      have : ((k : ℂ) + (l : ℂ)) = 2 * (n0 : ℂ) := by exact_mod_cast hn0
      linear_combination -(Complex.I * (x : ℂ) / 2) * this
    · intro n _ hn
      rw [if_neg (by omega), zero_mul]
    · intro h; exact absurd hn0mem h

open Filter Topology MeasureTheory

end

end


/-! # Sections 8–11: the serial circuit in Euler-angle coordinates, derivatives, analyticity, real coordinates -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 8. Serial circuit in Euler-angle (Rot) coordinates, `R_X` encoding, readout `Z` -/

def RZ (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * (a / 2)), 0; 0, Complex.exp (Complex.I * (a / 2))]

def RY (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.cos (a / 2) : ℝ) : ℂ), -((Real.sin (a / 2) : ℝ) : ℂ);
     ((Real.sin (a / 2) : ℝ) : ℂ), ((Real.cos (a / 2) : ℝ) : ℂ)]

/-- `Rot(φ, θ, ω) = RZ(ω) RY(θ) RZ(φ)` (PennyLane convention). -/
def Rot (φ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := RZ ω * RY θ * RZ φ

/-- A block of `tbl` stacked Rot gates; `Θ t = (φ, θ, ω)` of the `t`-th gate, gate `0` applied first. -/
def stackRot : (tbl : ℕ) → (Fin tbl → Fin 3 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | t + 1, Θ => Rot (Θ (Fin.last t) 0) (Θ (Fin.last t) 1) (Θ (Fin.last t) 2) *
      stackRot t (fun i => Θ (Fin.castSucc i))

/-- Readout observable. -/
def Zm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Parameters: block `ℓ = 0..L`, gate `t` within the block, Euler angle `c`. -/
abbrev Params (L tbl : ℕ) := Fin (L + 1) → Fin tbl → Fin 3 → ℝ
abbrev Idx (L tbl : ℕ) := Fin (L + 1) × Fin tbl × Fin 3

def circuitState (L tbl : ℕ) (θ : Params L tbl) (x : ℝ) : Fin 2 → ℂ :=
  serialState L (fun ℓ => stackRot tbl (θ ℓ)) x

/-- Model output `f_θ(x) = ⟨ψ|Z|ψ⟩`. -/
def model (L tbl : ℕ) (θ : Params L tbl) (x : ℝ) : ℝ :=
  (ip (circuitState L tbl θ x) (Zm *ᵥ circuitState L tbl θ x)).re

/-- Unit vector in parameter direction `j`. -/
def dirVec {L tbl : ℕ} (j : Idx L tbl) : Params L tbl :=
  fun ℓ t c => if (ℓ, t, c) = j then 1 else 0

/-- `RZ a` lies in SU(2). -/
theorem RZ_mem_SU2 (a : ℝ) : RZ a ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [RZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, ← Complex.exp_conj,
        ← Complex.exp_add, map_ofNat]
  · simp [RZ, Matrix.det_fin_two, ← Complex.exp_add]

/-- Complex conjugation fixes `cos (x / 2)` for real `x`. -/
theorem conj_cos_half (x : ℝ) : (starRingEnd ℂ) (Complex.cos (x / 2)) = Complex.cos (x / 2) := by
  rw [← Complex.cos_conj]; simp [map_ofNat]

/-- Complex conjugation fixes `sin (x / 2)` for real `x`. -/
theorem conj_sin_half (x : ℝ) : (starRingEnd ℂ) (Complex.sin (x / 2)) = Complex.sin (x / 2) := by
  rw [← Complex.sin_conj]; simp [map_ofNat]

/-- `RY a` lies in SU(2). -/
theorem RY_mem_SU2 (a : ℝ) : RY a ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have h := Complex.cos_sq_add_sin_sq ((a : ℂ) / 2)
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [RY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, conj_cos_half,
        conj_sin_half] <;> first | ring1 | linear_combination h
  · simp [RY, Matrix.det_fin_two]; linear_combination h

theorem rot_mem_SU2 (φ θ ω : ℝ) : Rot φ θ ω ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold Rot
  exact mul_mem (mul_mem (RZ_mem_SU2 ω) (RY_mem_SU2 θ)) (RZ_mem_SU2 φ)

theorem RXm_mem_SU2 (x : ℝ) : RXm x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have h := Complex.cos_sq_add_sin_sq ((x : ℂ) / 2)
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [RXm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, conj_cos_half,
        conj_sin_half] <;>
      first | ring1 | linear_combination h - (Complex.sin (x / 2)) ^ 2 * Complex.I_sq
  · simp [RXm, Matrix.det_fin_two]
    linear_combination h - (Complex.sin (x / 2)) ^ 2 * Complex.I_sq

/-- A serial state built from unitary blocks is normalised. -/
theorem serialState_normalised (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup (Fin 2) ℂ) (x : ℝ) :
    ip (serialState L V x) (serialState L V x) = 1 := by
  induction L with
  | zero => simp only [serialState]; rw [ip_unitary _ (hV 0)]; simp [ip]
  | succ L ih =>
    simp only [serialState]
    rw [ip_unitary _ (hV _), ip_unitary _ (RXm_mem_SU2 x).1]
    exact ih _ (fun i => hV _)

/-- The complex embedding of a real-analytic function is real-analytic. -/
theorem analyticAt_ofReal_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {p : E} (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (fun q => (f q : ℂ)) p :=
  (Complex.ofRealCLM.analyticAt (f p)).comp hf

/-- The complex exponential of a real-analytic function is real-analytic. -/
theorem analyticAt_cexp_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    {p : E} (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (fun q => Complex.exp (f q)) p :=
  ((analyticAt_cexp (z := f p)).restrictScalars (𝕜 := ℝ)).comp hf

/-- The entries of `RZ` along a real-analytic angle are real-analytic. -/
theorem analyticAt_RZ_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {p : E} (hf : AnalyticAt ℝ f p) (a b : Fin 2) : AnalyticAt ℝ (fun q => RZ (f q) a b) p := by
  have h1 := analyticAt_cexp_comp (p := p) (f := fun q => -Complex.I * ((f q : ℂ) / 2))
    (analyticAt_const.mul ((analyticAt_ofReal_comp hf).div_const))
  have h2 := analyticAt_cexp_comp (p := p) (f := fun q => Complex.I * ((f q : ℂ) / 2))
    (analyticAt_const.mul ((analyticAt_ofReal_comp hf).div_const))
  fin_cases a <;> fin_cases b
  · exact h1
  · exact analyticAt_const
  · exact analyticAt_const
  · exact h2

/-- The entries of `RY` along a real-analytic angle are real-analytic. -/
theorem analyticAt_RY_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {p : E} (hf : AnalyticAt ℝ f p) (a b : Fin 2) : AnalyticAt ℝ (fun q => RY (f q) a b) p := by
  have hc := analyticAt_ofReal_comp (Real.analyticAt_cos.comp (hf.div_const (c := (2 : ℝ))))
  have hs := analyticAt_ofReal_comp (Real.analyticAt_sin.comp (hf.div_const (c := (2 : ℝ))))
  fin_cases a <;> fin_cases b
  · exact hc
  · exact hs.neg
  · exact hs
  · exact hc

/-- Entrywise real-analyticity is preserved by matrix multiplication. -/
theorem analyticAt_mul_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M N : E → Matrix (Fin 2) (Fin 2) ℂ} {p : E}
    (hM : ∀ a b, AnalyticAt ℝ (fun q => M q a b) p) (hN : ∀ a b, AnalyticAt ℝ (fun q => N q a b) p)
    (a b : Fin 2) : AnalyticAt ℝ (fun q => (M q * N q) a b) p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hM a 0).mul (hN 0 b)).add ((hM a 1).mul (hN 1 b))

/-- Entrywise real-analyticity is preserved by matrix-vector multiplication. -/
theorem analyticAt_mulVec_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {v : E → Fin 2 → ℂ} {p : E}
    (hM : ∀ a b, AnalyticAt ℝ (fun q => M q a b) p) (hv : ∀ i, AnalyticAt ℝ (fun q => v q i) p)
    (i : Fin 2) : AnalyticAt ℝ (fun q => (M q *ᵥ v q) i) p := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact ((hM i 0).mul (hv 0)).add ((hM i 1).mul (hv 1))

/-- The entries of a Rot gate along real-analytic angles are real-analytic. -/
theorem analyticAt_Rot_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : E → ℝ} {p : E} (hf : AnalyticAt ℝ f p) (hg : AnalyticAt ℝ g p) (hh : AnalyticAt ℝ h p)
    (a b : Fin 2) : AnalyticAt ℝ (fun q => Rot (f q) (g q) (h q) a b) p :=
  analyticAt_mul_entry (analyticAt_mul_entry (analyticAt_RZ_entry hh) (analyticAt_RY_entry hg))
    (analyticAt_RZ_entry hf) a b

/-- The entries of a Rot-block stack along real-analytic angles are real-analytic. -/
theorem analyticAt_stackRot_entry (tbl : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Θ : E → Fin tbl → Fin 3 → ℝ) {p : E} (hΘ : ∀ t c, AnalyticAt ℝ (fun q => Θ q t c) p) :
    ∀ a b, AnalyticAt ℝ (fun q => stackRot tbl (Θ q) a b) p := by
  induction tbl with
  | zero => intro a b; exact analyticAt_const
  | succ t ih =>
    intro a b
    exact analyticAt_mul_entry (analyticAt_Rot_entry (hΘ _ 0) (hΘ _ 1) (hΘ _ 2))
      (ih (fun q i => Θ q (Fin.castSucc i)) (fun t c => hΘ _ c)) a b

/-- The amplitudes of a serial state with real-analytic blocks are real-analytic. -/
theorem analyticAt_serialState_entry (L : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) {p : E}
    (hV : ∀ ℓ a b, AnalyticAt ℝ (fun q => V q ℓ a b) p) (x : ℝ) :
    ∀ i, AnalyticAt ℝ (fun q => serialState L (V q) x i) p := by
  induction L with
  | zero =>
    intro i
    show AnalyticAt ℝ (fun q => (V q 0 *ᵥ ![1, 0]) i) p
    exact analyticAt_mulVec_entry (v := fun _ => ![1, 0]) (hV 0) (fun _ => analyticAt_const) i
  | succ L ih =>
    intro i
    show AnalyticAt ℝ (fun q => (V q (Fin.last (L + 1)) *ᵥ
      (RXm x *ᵥ serialState L (fun ℓ => V q (Fin.castSucc ℓ)) x)) i) p
    exact analyticAt_mulVec_entry (hV _)
      (analyticAt_mulVec_entry (M := fun _ => RXm x) (fun _ _ => analyticAt_const)
        (ih (fun q ℓ => V q (Fin.castSucc ℓ)) (fun ℓ => hV _))) i

/-- Each coordinate of the parameter vector is a real-analytic function of the parameters. -/
theorem analyticAt_param_coord {L tbl : ℕ} (ℓ : Fin (L + 1)) (t : Fin tbl) (c : Fin 3)
    (θ : Params L tbl) : AnalyticAt ℝ (fun θ' : Params L tbl => θ' ℓ t c) θ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) c).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin tbl => Fin 3 → ℝ) t).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Fin tbl → Fin 3 → ℝ) ℓ))).analyticAt θ

/-- The circuit amplitudes are real-analytic functions of the parameters. -/
theorem analyticAt_circuitState (L tbl : ℕ) (x : ℝ) (θ : Params L tbl) (i : Fin 2) :
    AnalyticAt ℝ (fun θ' : Params L tbl => circuitState L tbl θ' x i) θ :=
  analyticAt_serialState_entry L (fun (θ' : Params L tbl) ℓ => stackRot tbl (θ' ℓ))
    (fun ℓ => analyticAt_stackRot_entry tbl (fun (θ' : Params L tbl) => θ' ℓ)
      (fun t c => analyticAt_param_coord ℓ t c θ)) x i

/-- The readout observable `Z` is Hermitian. -/
theorem Zm_hermitian : Zmᴴ = Zm := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Zm]

/-! ## 9. Derivatives of the serial state and degree of the pairing ⟨Tψ, ·⟩ -/

/-- The pairing `⟨Tψ, Gψ⟩` of a serial state with itself is a trigonometric polynomial of degree ≤ `ℓ`. -/
theorem serialState_pairing_trig (ℓ : ℕ) (V : Fin (ℓ + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(ℓ : ℤ)) ℓ → a k = 0) ∧
      ∀ x, ip (T (serialState ℓ V x)) (G *ᵥ serialState ℓ V x) = trig ℓ a x := by
  obtain ⟨c, hc, hrep⟩ := serialState_expansion ℓ V
  obtain ⟨a, ha, haeq⟩ := pairing_integer_frequencies ℓ c c hc hc G
  refine ⟨a, ha, fun x => ?_⟩
  have hψ : serialState ℓ V x = fun i => ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ,
      c i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) := funext (hrep x)
  rw [hψ]
  exact haeq x

/-- Derivative of a state along a curve of blocks: the product rule applied block by block. -/
def dSerial : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) →
    (Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → Fin 2 → ℂ
  | 0, _, dV, _ => dV 0 *ᵥ ![1, 0]
  | L + 1, V, dV, x =>
      dV (Fin.last (L + 1)) *ᵥ (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x) +
      V (Fin.last (L + 1)) *ᵥ
        (RXm x *ᵥ dSerial L (fun i => V (Fin.castSucc i)) (fun i => dV (Fin.castSucc i)) x)

/-- Product rule for a matrix-vector product along a curve. -/
theorem hasDerivAt_mulVec_curve (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (dM : Matrix (Fin 2) (Fin 2) ℂ)
    (v : ℝ → Fin 2 → ℂ) (dv : Fin 2 → ℂ) (hM : ∀ a b, HasDerivAt (fun s => M s a b) (dM a b) 0)
    (hv : HasDerivAt v dv 0) :
    HasDerivAt (fun s => M s *ᵥ v s) (dM *ᵥ v 0 + M 0 *ᵥ dv) 0 := by
  apply hasDerivAt_pi.2
  intro i
  have h0 := hasDerivAt_pi.1 hv 0
  have h1 := hasDerivAt_pi.1 hv 1
  have h := ((hM i 0).mul h0).add ((hM i 1).mul h1)
  convert h using 1
  · funext s
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  · simp [mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The serial state along a differentiable curve of blocks has derivative `dSerial`. -/
theorem serialState_hasDerivAt (L : ℕ) (V : ℝ → Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (dV : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ ℓ a b, HasDerivAt (fun s => V s ℓ a b) (dV ℓ a b) 0) (x : ℝ) :
    HasDerivAt (fun s => serialState L (V s) x) (dSerial L (V 0) dV x) 0 := by
  induction L with
  | zero =>
    have h := hasDerivAt_mulVec_curve (fun s => V s 0) (dV 0) (fun _ => ![1, 0]) 0 (hV 0)
      (hasDerivAt_const _ _)
    simpa [dSerial] using h
  | succ L ih =>
    have h1 := ih (fun s i => V s (Fin.castSucc i)) (fun i => dV (Fin.castSucc i)) (fun ℓ => hV _)
    have h2 := hasDerivAt_mulVec_curve (fun _ => RXm x) 0 _ _
      (fun a b => by simpa using hasDerivAt_const (0 : ℝ) (RXm x a b)) h1
    have h3 := hasDerivAt_mulVec_curve (fun s => V s (Fin.last (L + 1))) (dV _) _ _ (hV _) h2
    convert h3 using 1
    simp only [dSerial, zero_mulVec, zero_add]

/-- `ip` is additive in its second argument. -/
theorem ip_add_right (u v w : Fin 2 → ℂ) : ip u (v + w) = ip u v + ip u w := by
  simp only [ip, Pi.add_apply]; ring

/-- For unitary `V`, `(D Vᴴ)(V w) = D w`. -/
theorem mulVec_star_unitary (D V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (w : Fin 2 → ℂ) : (D * star V) *ᵥ (V *ᵥ w) = D *ᵥ w := by
  rw [mulVec_mulVec, mul_assoc, (Matrix.mem_unitaryGroup_iff').1 hV, mul_one]

/-- `trig` is additive in its coefficients. -/
theorem trig_add (L : ℕ) (a b : ℤ → ℂ) (x : ℝ) : trig L (a + b) x = trig L a x + trig L b x := by
  simp only [trig, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Raising the nominal degree does not change a trigonometric polynomial of lower degree. -/
theorem trig_eq_of_le (L L' : ℕ) (hL : L ≤ L') (a : ℤ → ℂ)
    (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) (x : ℝ) : trig L' a x = trig L a x := by
  unfold trig
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k _ hk
    rw [ha k hk, zero_mul]

/-- Degree filtration for `dSerial`: if only blocks `≤ n` vary, `⟨Tψ, dψ⟩` has degree ≤ `min n L`. -/
theorem dSerial_pairing_trig (L : ℕ) (V dV : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ i, V i ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (n : ℕ)
    (hdV : ∀ i : Fin (L + 1), n < (i : ℕ) → dV i = 0) :
    ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(n : ℤ)) n → a k = 0) ∧
      (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
      ∀ x, ip (T (serialState L V x)) (dSerial L V dV x) = trig L a x := by
  induction L with
  | zero =>
    obtain ⟨a, ha, haeq⟩ := serialState_pairing_trig 0 V (dV 0 * star (V 0))
    refine ⟨a, fun k hk => ha k ?_, ha, fun x => ?_⟩
    · intro h
      apply hk
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · rw [← haeq x]
      show _ = ip _ ((dV 0 * star (V 0)) *ᵥ (V 0 *ᵥ ![1, 0]))
      rw [mulVec_star_unitary _ _ (hV 0).1]
      rfl
  | succ L ih =>
    obtain ⟨a1, ha1n, ha1L, ha1⟩ := ih (fun i => V (Fin.castSucc i)) (fun i => dV (Fin.castSucc i))
      (fun i => hV _) (fun i hi => hdV _ (by simpa using hi))
    have hB : ∀ x, ip (T (serialState (L + 1) V x)) (V (Fin.last (L + 1)) *ᵥ (RXm x *ᵥ
        dSerial L (fun i => V (Fin.castSucc i)) (fun i => dV (Fin.castSucc i)) x)) = trig L a1 x := by
      intro x
      show ip (T (V (Fin.last (L + 1)) *ᵥ
        (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x))) _ = _
      rw [mulVec_mulVec, mulVec_mulVec, gauge_invariance _ (mul_mem (hV _) (RXm_mem_SU2 x))]
      exact ha1 x
    have hsplit : ∀ x, ip (T (serialState (L + 1) V x)) (dSerial (L + 1) V dV x) =
        ip (T (serialState (L + 1) V x)) (dV (Fin.last (L + 1)) *ᵥ
          (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x)) + trig L a1 x := by
      intro x
      rw [← hB x]
      exact ip_add_right _ _ _
    have ha1L' : ∀ x, trig (L + 1) a1 x = trig L a1 x :=
      fun x => trig_eq_of_le L (L + 1) (Nat.le_succ L) a1 ha1L x
    by_cases hn : L + 1 ≤ n
    · obtain ⟨a2, ha2, ha2eq⟩ := serialState_pairing_trig (L + 1) V
        (dV (Fin.last (L + 1)) * star (V (Fin.last (L + 1))))
      refine ⟨a1 + a2, ?_, ?_, fun x => ?_⟩
      · intro k hk
        have hk' : k ∉ Finset.Icc (-((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ) := by
          intro h; apply hk
          simp only [Finset.mem_Icc] at h ⊢
          omega
        simp only [Pi.add_apply, ha1n k hk, ha2 k hk', add_zero]
      · intro k hk
        have hk' : k ∉ Finset.Icc (-(L : ℤ)) L := by
          intro h; apply hk
          simp only [Finset.mem_Icc] at h ⊢
          omega
        simp only [Pi.add_apply, ha1L k hk', ha2 k hk, add_zero]
      · have hA : ip (T (serialState (L + 1) V x)) (dV (Fin.last (L + 1)) *ᵥ
            (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x)) = trig (L + 1) a2 x := by
          rw [← ha2eq x]
          congr 1
          show _ = (dV (Fin.last (L + 1)) * star (V (Fin.last (L + 1)))) *ᵥ
            (V (Fin.last (L + 1)) *ᵥ (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x))
          rw [mulVec_star_unitary _ _ (hV _).1]
        rw [hsplit x, hA, trig_add, ha1L' x, add_comm]
    · have hz : dV (Fin.last (L + 1)) = 0 := hdV _ (by simp; omega)
      refine ⟨a1, ha1n, fun k hk => ha1L k ?_, fun x => ?_⟩
      · intro h; apply hk
        simp only [Finset.mem_Icc] at h ⊢
        omega
      · rw [hsplit x, hz, zero_mulVec, ha1L' x]
        simp [ip]

/-- Orthogonality of the Fourier modes on `[0, 2π]`: coefficient extraction from a finite sum. -/
theorem fourier_coeff_sum (S : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ x in (0 : ℝ)..(2 * Real.pi),
      (∑ n ∈ S, c n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
        Complex.exp (-(Complex.I * (m : ℂ) * (x : ℂ))) = if m ∈ S then c m else 0 := by
  have hint : ∀ n : ℤ, ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) *
      Complex.exp (-(Complex.I * (m : ℂ) * (x : ℂ))) = if n = m then (2 * Real.pi : ℂ) else 0 := by
    intro n
    have he : ∀ x : ℝ, Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) *
        Complex.exp (-(Complex.I * (m : ℂ) * (x : ℂ))) =
          Complex.exp ((Complex.I * ((n - m : ℤ) : ℂ)) * (x : ℂ)) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [he]
    split_ifs with h
    · subst h
      simp
    · have hc : Complex.I * ((n - m : ℤ) : ℂ) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast sub_ne_zero.mpr h)
      have h1 : Complex.exp (Complex.I * ((n - m : ℤ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
        rw [Complex.exp_eq_one_iff]
        exact ⟨n - m, by push_cast; ring⟩
      rw [integral_exp_mul_complex hc, h1]
      simp
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum]
  · have hc : ∀ n : ℤ, ∫ x in (0 : ℝ)..(2 * Real.pi), c n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) *
        Complex.exp (-(Complex.I * (m : ℂ) * (x : ℂ))) = c n * if n = m then (2 * Real.pi : ℂ) else 0 := by
      intro n
      rw [← hint n, ← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [hc]
    rw [Finset.mul_sum]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' S m]
    split_ifs
    · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    · rfl
  · intro n _
    apply Continuous.intervalIntegrable
    fun_prop

/-! ## 10. Analyticity of the circuit in Euler angles -/

/-- The complex conjugate of a real-analytic function is real-analytic. -/
theorem analyticAt_conj_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    {p : E} (hf : AnalyticAt ℝ f p) : AnalyticAt ℝ (fun q => (starRingEnd ℂ) (f q)) p :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt (f p)).comp hf

theorem model_analytic (L tbl : ℕ) (x : ℝ) :
    AnalyticOnNhd ℝ (fun θ : Params L tbl => model L tbl θ x) Set.univ := by
  intro θ _
  have hψ := analyticAt_circuitState L tbl x θ
  have hZ := analyticAt_mulVec_entry (M := fun _ => Zm) (fun _ _ => analyticAt_const) hψ
  have hip : AnalyticAt ℝ (fun θ' => ip (circuitState L tbl θ' x) (Zm *ᵥ circuitState L tbl θ' x)) θ :=
    ((analyticAt_conj_comp (hψ 0)).mul (hZ 0)).add ((analyticAt_conj_comp (hψ 1)).mul (hZ 1))
  exact (Complex.reCLM.analyticAt _).comp hip

/-- Every parity-`ℓ` half-integer expansion is `T` applied to another such expansion. -/
theorem expansion_eq_T (ℓ : ℕ) (c : Fin 2 → ℤ → ℂ)
    (hc : ∀ i k, c i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ)) :
    ∃ c' : Fin 2 → ℤ → ℂ, (∀ i k, c' i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ)) ∧
      ∀ x : ℝ, (fun i => ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ,
          c i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2)) =
        T (fun i => ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ,
          c' i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2)) := by
  have hconj : ∀ (d : ℤ → ℂ) (x : ℝ), (starRingEnd ℂ) (∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ,
      (starRingEnd ℂ) (d (-k)) * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2)) =
      ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ, d k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) := by
    intro d x
    rw [map_sum]
    apply Finset.sum_nbij' (fun k => -k) (fun k => -k)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
      congr 2
      simp only [map_div₀, map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal,
        map_ofNat, Int.cast_neg]
      ring
  refine ⟨![fun k => (starRingEnd ℂ) (c 1 (-k)), fun k => -(starRingEnd ℂ) (c 0 (-k))], ?_, ?_⟩
  · have hneg : ∀ i k, c i (-k) ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ) := by
      intro i k h
      obtain ⟨h1, h2⟩ := hc i (-k) h
      simp only [Finset.mem_Icc, Int.even_iff] at h1 h2 ⊢
      omega
    intro i k h
    fin_cases i
    · exact hneg 1 k (fun h' => h (by simp [h']))
    · exact hneg 0 k (fun h' => h (by simp [h']))
  · intro x
    funext i
    fin_cases i
    · simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.isValue]
      simp only [neg_mul, Finset.sum_neg_distrib, map_neg, neg_neg]
      exact (hconj (c 0) x).symm
    · simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one, Fin.isValue]
      exact (hconj (c 1) x).symm

/-! ## 11. Real coordinates, the envelope matrix A_μ, and Euler surjectivity -/

/-- Real representation (Re c₀, Re c₁, Im c₁, …, Re c_L, Im c_L) of a coefficient sequence. -/
def realRep (L : ℕ) (c : ℤ → ℂ) : Fin (2 * L + 1) → ℝ := fun r =>
  if (r : ℕ) = 0 then (c 0).re
  else if (r : ℕ) % 2 = 1 then (c ((((r : ℕ) + 1) / 2 : ℕ) : ℤ)).re
  else (c (((r : ℕ) / 2 : ℕ) : ℤ)).im

/-- Real coordinates (Re a_k, Im a_k), k = −L … L, of a coefficient sequence supported in [−L, L]. -/
def coeffVec (L : ℕ) (a : ℤ → ℂ) : Fin (2 * (2 * L + 1)) → ℝ := fun s =>
  if (s : ℕ) % 2 = 0 then (a ((((s : ℕ) / 2 : ℕ) : ℤ) - L)).re else (a ((((s : ℕ) / 2 : ℕ) : ℤ) - L)).im

/-- The real basis vector of index `s`: `1` or `i` at frequency `s/2 − L`. -/
def coeffBasis (L : ℕ) (s : Fin (2 * (2 * L + 1))) : ℤ → ℂ := fun k =>
  if k = (((s : ℕ) / 2 : ℕ) : ℤ) - L then (if (s : ℕ) % 2 = 0 then 1 else Complex.I) else 0

/-- Matrix of the envelope operator A_μ in real coordinates, determined by the envelope coefficients `b` alone. -/
def envMatrix (L : ℕ) (b : ℤ → ℂ) : Matrix (Fin (2 * L + 1)) (Fin (2 * (2 * L + 1))) ℝ :=
  fun r s => realRep L (fun m => envCoeff L (coeffBasis L s) b m) r

/-- A sequence supported in `[-L, L]` is the real combination of `coeffBasis` with coordinates `coeffVec`. -/
theorem coeffBasis_expansion (L : ℕ) (a : ℤ → ℂ) (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) (k : ℤ) :
    a k = ∑ s, (coeffVec L a s : ℂ) * coeffBasis L s k := by
  by_cases hk : k ∈ Finset.Icc (-(L : ℤ)) L
  · simp only [Finset.mem_Icc] at hk
    set n := (k + L).toNat with hn
    have hnk : ((n : ℕ) : ℤ) = k + L := by omega
    rw [Finset.sum_eq_add (⟨2 * n, by omega⟩ : Fin (2 * (2 * L + 1))) ⟨2 * n + 1, by omega⟩
      (by simp [Fin.ext_iff]) ?_ (by simp) (by simp)]
    · have e1 : (2 * n) / 2 = n := by omega
      have e2 : (2 * n + 1) / 2 = n := by omega
      have e3 : ((n : ℕ) : ℤ) - L = k := by omega
      have m1 : (2 * n) % 2 = 0 := by omega
      have m2 : (2 * n + 1) % 2 = 1 := by omega
      simp only [coeffVec, coeffBasis, e1, e2, e3, m1, m2, if_true]
      norm_num
    · intro c _ hc
      have : k ≠ (((c : ℕ) / 2 : ℕ) : ℤ) - L := by
        intro h
        obtain ⟨h1, h2⟩ := hc
        rcases Nat.even_or_odd' (c : ℕ) with ⟨q, hq | hq⟩
        · exact h1 (Fin.ext (by simp only; omega))
        · exact h2 (Fin.ext (by simp only; omega))
      simp only [coeffBasis]
      rw [if_neg this, mul_zero]
  · rw [ha k hk]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have : k ≠ (((s : ℕ) / 2 : ℕ) : ℤ) - L := by
      intro h
      apply hk
      have := s.isLt
      simp only [Finset.mem_Icc]
      omega
    simp only [coeffBasis]
    rw [if_neg this, mul_zero]

/-- `envCoeff` is ℝ-linear in its first argument, for finite real combinations. -/
theorem envCoeff_real_sum {ι : Type*} [Fintype ι] (L : ℕ) (r : ι → ℝ) (f : ι → ℤ → ℂ) (b : ℤ → ℂ) (m : ℤ) :
    envCoeff L (fun k => ∑ s, (r s : ℂ) * f s k) b m = ∑ s, (r s : ℂ) * envCoeff L (f s) b m := by
  simp only [envCoeff, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => by ring

/-- `realRep` is ℝ-linear, for finite real combinations. -/
theorem realRep_real_sum {ι : Type*} [Fintype ι] (L : ℕ) (r : ι → ℝ) (c : ι → ℤ → ℂ)
    (i : Fin (2 * L + 1)) :
    realRep L (fun m => ∑ s, (r s : ℂ) * c s m) i = ∑ s, r s * realRep L (c s) i := by
  unfold realRep
  split_ifs <;> simp [Complex.re_sum, Complex.im_sum]

/-- `realRep` only reads coefficients with index in `[-L, L]`. -/
theorem realRep_congr (L : ℕ) (c c' : ℤ → ℂ) (h : ∀ m ∈ Finset.Icc (-(L : ℤ)) L, c m = c' m) :
    realRep L c = realRep L c' := by
  funext i
  have hi := i.isLt
  unfold realRep
  split_ifs
  · rw [h 0 (by simp)]
  · rw [h _ (by simp only [Finset.mem_Icc]; omega)]
  · rw [h _ (by simp only [Finset.mem_Icc]; omega)]

/-- Entries of a Rot gate in closed form. -/
theorem Rot_entries (φ θ ω : ℝ) :
    Rot φ θ ω = !![((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (-Complex.I * ((ω / 2 : ℝ) + (φ / 2 : ℝ))),
        -((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ / 2 : ℝ) - (ω / 2 : ℝ)));
      ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((ω / 2 : ℝ) - (φ / 2 : ℝ))),
        ((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((ω / 2 : ℝ) + (φ / 2 : ℝ)))] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp only [Rot, RZ, RY, Matrix.mul_apply, Fin.sum_univ_two] <;> simp <;>
    rw [mul_comm (Complex.exp _) _, mul_assoc, ← Complex.exp_add] <;> congr 2 <;> ring

/-- Entry relations of an element of SU(2): `U₁₁ = conj U₀₀`, `U₀₁ = -conj U₁₀`, `|U₀₀|² + |U₁₀|² = 1`. -/
theorem SU2_entries (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U 1 1 = (starRingEnd ℂ) (U 0 0) ∧ U 0 1 = -(starRingEnd ℂ) (U 1 0) ∧
      ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff'] at hU
  obtain ⟨hu, hdet⟩ := hU
  have hadj : U * U.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hs : star U = U.adjugate := by
    calc star U = star U * (U * U.adjugate) := by rw [hadj, mul_one]
      _ = (star U * U) * U.adjugate := by rw [mul_assoc]
      _ = U.adjugate := by rw [hu, one_mul]
  rw [Matrix.adjugate_fin_two] at hs
  have e1 := congrFun (congrFun hs 0) 0
  have e2 := congrFun (congrFun hs 0) 1
  simp [Matrix.star_apply] at e1 e2
  have h11 : U 1 1 = (starRingEnd ℂ) (U 0 0) := e1.symm
  have h01 : U 0 1 = -(starRingEnd ℂ) (U 1 0) := by rw [e2]; ring
  refine ⟨h11, h01, ?_⟩
  rw [Matrix.det_fin_two, h11, h01] at hdet
  have h := congrArg Complex.re hdet
  simp [Complex.mul_re] at h
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  linarith

/-- Euler surjectivity: every element of SU(2) is a Rot gate. -/
theorem rot_surjective (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ φ θ ω : ℝ, Rot φ θ ω = U := by
  obtain ⟨h11, h01, hn⟩ := SU2_entries U hU
  have hα1 : ‖U 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (U 0 0), norm_nonneg (U 1 0)]
  have hc : Real.cos (Real.arccos ‖U 0 0‖) = ‖U 0 0‖ :=
    Real.cos_arccos (by linarith [norm_nonneg (U 0 0)]) hα1
  have hs : Real.sin (Real.arccos ‖U 0 0‖) = ‖U 1 0‖ := by
    rw [Real.sin_arccos, show 1 - ‖U 0 0‖ ^ 2 = ‖U 1 0‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  have hα := Complex.norm_mul_exp_arg_mul_I (U 0 0)
  have hβ := Complex.norm_mul_exp_arg_mul_I (U 1 0)
  have hαc : (starRingEnd ℂ) (U 0 0) =
      ↑‖U 0 0‖ * Complex.exp (-(↑(U 0 0).arg * Complex.I)) := by
    conv_lhs => rw [← hα]
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 2; simp
  have hβc : (starRingEnd ℂ) (U 1 0) =
      ↑‖U 1 0‖ * Complex.exp (-(↑(U 1 0).arg * Complex.I)) := by
    conv_lhs => rw [← hβ]
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 2; simp
  refine ⟨-((U 0 0).arg + (U 1 0).arg), 2 * Real.arccos ‖U 0 0‖, (U 1 0).arg - (U 0 0).arg, ?_⟩
  rw [Rot_entries, show 2 * Real.arccos ‖U 0 0‖ / 2 = Real.arccos ‖U 0 0‖ by ring, hc, hs]
  ext i k
  fin_cases i <;> fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    conv_rhs => rw [← hα]
    congr 2; push_cast; ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    rw [h01, hβc, neg_mul]
    congr 3; push_cast; ring
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    conv_rhs => rw [← hβ]
    congr 2; push_cast; ring
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    rw [h11, hαc]
    congr 2; push_cast; ring

end

end


/-! # Part II — the results of the paper

Sections 12–24 state the results of the paper (Lemma 3.2, Lemma 3.3, Lemma 4.1, Lemma 4.2, Remark 4.3, Eq. (2),
Proposition 4.4, Corollary 4.5, Lemma B.1, Lemma B.2, Lemma B.3) at the level of gates, as in the paper;
Sections 1–11 are the verified machinery they reuse. Results the paper cites enter as explicit hypotheses
(Section 12); nothing is added as an axiom. -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 12. Cited results, as hypotheses -/

/-- Fejér–Riesz: a nonnegative trigonometric polynomial of degree ≤ L is `|p(e^{ix})|²` for a polynomial `p` of
    degree ≤ L. -/
def FejerRieszHyp : Prop :=
  ∀ (L : ℕ) (c : ℤ → ℂ), (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0) →
    (∀ x, (trig L c x).im = 0 ∧ 0 ≤ (trig L c x).re) →
    ∃ p : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (0 : ℤ) L → p k = 0) ∧
      ∀ x, trig L c x = ((Complex.normSq (trig L p x) : ℝ) : ℂ)

/-- Signal operator `diag(1, e^{ix})` of generalised quantum signal processing. -/
def sigMat (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.exp (Complex.I * (x : ℂ))]

/-- `U_L diag(1, e^{ix}) U_{L−1} ⋯ diag(1, e^{ix}) U_0 e₀`. -/
def sigState : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → Fin 2 → ℂ
  | 0, U, _ => U 0 *ᵥ ![1, 0]
  | L + 1, U, x => U (Fin.last (L + 1)) *ᵥ (sigMat x *ᵥ sigState L (fun i => U (Fin.castSucc i)) x)

/-- Generalised quantum signal processing (Motlagh & Wiebe 2024): every pair of polynomials of degree ≤ L in
    `e^{ix}` with `|p|² + |q|² = 1` on the circle is, up to a constant phase, the first column of an `L`-layer
    sequence of SU(2) elements with signal `diag(1, e^{ix})`. -/
def GQSPHyp : Prop :=
  ∀ (L : ℕ) (p q : ℤ → ℂ), (∀ k, k ∉ Finset.Icc (0 : ℤ) L → p k = 0) →
    (∀ k, k ∉ Finset.Icc (0 : ℤ) L → q k = 0) →
    (∀ x, Complex.normSq (trig L p x) + Complex.normSq (trig L q x) = 1) →
    ∃ U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ, (∀ ℓ, U ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ x, sigState L U x = φ • ![trig L p x, trig L q x]

/-- Sard's theorem (smooth case): the critical values of a smooth map `ℝⁿ → ℝᵐ` form a Lebesgue-null set.
    (Formalisation note: the original text wrote `LinearMap.range (fderiv ℝ F θ)`, which does not elaborate; the
    Fréchet derivative is now coerced explicitly to a linear map. The meaning is unchanged.) -/
def SardHyp : Prop :=
  ∀ (n m : ℕ) (F : (Fin n → ℝ) → (Fin m → ℝ)), (∀ k : ℕ, ContDiff ℝ k F) →
    MeasureTheory.volume (F '' {θ | LinearMap.range (fderiv ℝ F θ : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) ≠ ⊤}) = 0

/-- Real and imaginary parts of the entries of a tuple of matrices. -/
def reIm {ι n : Type*} (G : ι → Matrix n n ℂ) : ι × n × n × Bool → ℝ :=
  fun p => if p.2.2.2 then (G p.1 p.2.1 p.2.2.1).re else (G p.1 p.2.1 p.2.2.1).im

/-- Null zero sets on SU(d)^m (Mityagin 2020, with Haar measure absolutely continuous in charts): a real polynomial
    in the real and imaginary parts of the gate entries that is nonzero at one point of SU(d)^m vanishes on a
    `μ`-null subset of SU(d)^m. For the Haar measure `μ` this is the cited result. -/
def HaarNullHyp {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (μ : MeasureTheory.Measure (ι → n → n → ℂ)) : Prop :=
  ∀ q : MvPolynomial (ι × n × n × Bool) ℝ,
    (∃ G₀ : ι → Matrix n n ℂ, (∀ i, G₀ i ∈ Matrix.specialUnitaryGroup n ℂ) ∧
      MvPolynomial.eval (reIm G₀) q ≠ 0) →
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup n ℂ) ∧
      MvPolynomial.eval (reIm (fun i => Matrix.of (G i))) q = 0} = 0

/-! ## 13. Fourier coefficients and the design matrix -/

/-- Fourier coefficient `c_m` of a real function on `[0, 2π]`.
    (Formalisation note: called `fourierCoeff` in the original text; renamed because Mathlib already defines
    `fourierCoeff`. The definition is unchanged.) -/
def realFourierCoeff (f : ℝ → ℝ) (m : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ x in (0 : ℝ)..(2 * Real.pi), (f x : ℂ) * Complex.exp (-(Complex.I * (m : ℂ) * (x : ℂ)))

/-- Real Fourier design matrix of the inputs `x`: columns `1, 2 cos kx, −2 sin kx` in the order of `realRep`. -/
def designMatrix (L : ℕ) {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin (2 * L + 1)) ℝ :=
  fun i r =>
    if (r : ℕ) = 0 then 1
    else if (r : ℕ) % 2 = 1 then 2 * Real.cos ((((r : ℕ) + 1) / 2 : ℕ) * x i)
    else -2 * Real.sin (((r : ℕ) / 2 : ℕ) * x i)

/-- One row of the design matrix. -/
def designEntry (L : ℕ) (x : ℝ) (r : Fin (2 * L + 1)) : ℝ := designMatrix L (fun _ : Fin 1 => x) 0 r

/-- Splitting a symmetric integer sum into the zero term and pairs `±(k+1)`. -/
theorem sum_Icc_symm_split (n : ℕ) (h : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, h k = h 0 + ∑ k ∈ Finset.range n, (h (k + 1) + h (-(k + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
    ring

/-- Splitting a sum over `Fin (2L+1)` into index `0` and the pairs `2k+1, 2k+2`. -/
theorem sum_fin_odd_split (L : ℕ) (φ : ℕ → ℝ) :
    ∑ r : Fin (2 * L + 1), φ r = φ 0 + ∑ k ∈ Finset.range L, (φ (2 * k + 1) + φ (2 * k + 2)) := by
  rw [Fin.sum_univ_eq_sum_range φ (2 * L + 1)]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 2 * (L + 1) + 1 = 2 * L + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring_nf

/-- Complex conjugate of a trigonometric polynomial. -/
theorem trig_conj (L : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    (starRingEnd ℂ) (trig L c x) = trig L (fun k => (starRingEnd ℂ) (c (-k))) x := by
  unfold trig
  rw [map_sum]
  apply Finset.sum_nbij' (fun k => -k) (fun k => -k)
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k _; simp
  · intro k _; simp
  · intro k _
    simp only [map_mul, neg_neg, ← Complex.exp_conj, Complex.conj_I, map_intCast, Complex.conj_ofReal]
    congr 2
    push_cast; ring

/-- Uniqueness of the coefficients of a trigonometric polynomial. -/
theorem trig_coeff_unique (L : ℕ) (a b : ℤ → ℂ) (h : ∀ x, trig L a x = trig L b x) :
    ∀ k ∈ Finset.Icc (-(L : ℤ)) L, a k = b k := by
  intro k hk
  have := fourier_coeff_sum (Finset.Icc (-(L : ℤ)) L) a k
  have h2 := fourier_coeff_sum (Finset.Icc (-(L : ℤ)) L) b k
  rw [if_pos hk] at this h2
  rw [← this, ← h2]
  congr 2
  funext x
  have := h x
  unfold trig at this
  rw [this]

theorem re_mul_exp (c : ℂ) (k : ℤ) (x : ℝ) :
    (c * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))).re =
      c.re * Real.cos (k * x) - c.im * Real.sin (k * x) := by
  rw [show Complex.I * (k : ℂ) * (x : ℂ) = ((k * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- A real-valued trigonometric polynomial of degree ≤ L is the design matrix applied to the real representation of
    its coefficients. -/
theorem real_trig_eq_design (L : ℕ) (c : ℤ → ℂ) (hc : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0)
    (g : ℝ → ℝ) (hg : ∀ x, ((g x : ℝ) : ℂ) = trig L c x) {n : ℕ} (x : Fin n → ℝ) :
    (fun i => g (x i)) = designMatrix L x *ᵥ realRep L c := by
  have hsymm : ∀ k, c (-k) = (starRingEnd ℂ) (c k) := by
    have h1 : ∀ x, trig L c x = trig L (fun k => (starRingEnd ℂ) (c (-k))) x := by
      intro x
      rw [← trig_conj, ← hg, Complex.conj_ofReal]
    intro k
    by_cases hk : k ∈ Finset.Icc (-(L : ℤ)) L
    · have hk' : -k ∈ Finset.Icc (-(L : ℤ)) L := by simp only [Finset.mem_Icc] at hk ⊢; omega
      have := trig_coeff_unique L _ _ h1 (-k) hk'
      rw [this]; simp
    · have hk' : -k ∉ Finset.Icc (-(L : ℤ)) L := by simp only [Finset.mem_Icc] at hk ⊢; omega
      rw [hc k hk, hc _ hk', map_zero]
  funext i
  have hgx : g (x i) = (trig L c (x i)).re := by rw [← hg]; simp
  rw [hgx, trig, Complex.re_sum]
  simp only [re_mul_exp]
  rw [sum_Icc_symm_split]
  simp only [mulVec, dotProduct, designMatrix, realRep]
  rw [sum_fin_odd_split L (fun r : ℕ => (if r = 0 then (1 : ℝ) else if r % 2 = 1 then
      2 * Real.cos (((r + 1) / 2 : ℕ) * x i) else -2 * Real.sin ((r / 2 : ℕ) * x i)) *
      (if r = 0 then (c 0).re else if r % 2 = 1 then
      (c (((r + 1) / 2 : ℕ) : ℤ)).re else (c ((r / 2 : ℕ) : ℤ)).im))]
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero, if_true]
  rw [one_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have e2 : (2 * k + 2) / 2 = k + 1 := by omega
  have e3 : (2 * k + 1) % 2 = 1 := by omega
  have e4 : (2 * k + 2) % 2 = 0 := by omega
  simp only [e1, e3, e4, show 2 * k + 1 ≠ 0 by omega, show 2 * k + 2 ≠ 0 by omega, if_false, if_true,
    show (0:ℕ) ≠ 1 by omega]
  rw [hsymm]
  simp only [Complex.conj_re, Complex.conj_im]
  push_cast
  rw [show -((k : ℝ) + 1) * x i = -(((k : ℝ) + 1) * x i) by ring, Real.cos_neg, Real.sin_neg]
  ring

/-- `2L+1` equispaced points with offset `x₀` (the experiments use `x₀ = −π`). -/
def eqGrid (L : ℕ) (x₀ : ℝ) : Fin (2 * L + 1) → ℝ := fun k => x₀ + 2 * Real.pi * (k : ℝ) / (2 * L + 1)

/-- Exponential sums over the equispaced grid vanish at nonzero frequencies `|m| ≤ 2L`. -/
theorem eqGrid_exp_sum (L : ℕ) (x₀ : ℝ) (m : ℤ) (hm : m ≠ 0) (hm' : |m| ≤ 2 * L) :
    ∑ k : Fin (2 * L + 1), Complex.exp (Complex.I * (m : ℂ) * (eqGrid L x₀ k : ℂ)) = 0 := by
  set N := 2 * L + 1 with hN
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) with hζ
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (by omega)
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hterm : ∀ k : Fin N, Complex.exp (Complex.I * (m : ℂ) * (eqGrid L x₀ k : ℂ)) =
      Complex.exp (Complex.I * (m : ℂ) * (x₀ : ℂ)) * (ζ ^ m) ^ (k : ℕ) := by
    intro k
    rw [hζ, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [eqGrid, hN]
    push_cast
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun k => (ζ ^ m) ^ k) N]
  have hne : ζ ^ m ≠ 1 := by
    intro h
    rw [hprim.zpow_eq_one_iff_dvd] at h
    obtain ⟨d, hd⟩ := h
    have : d ≠ 0 := by rintro rfl; simp at hd; exact hm hd
    have h1 : (N : ℤ) ≤ |m| := by
      rw [hd, abs_mul]
      have : (1 : ℤ) ≤ |d| := Int.one_le_abs this
      have : (0 : ℤ) ≤ |(N : ℤ)| := abs_nonneg _
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (N : ℤ))]
      nlinarith
    push_cast [hN] at h1
    omega
  have hN1 : (ζ ^ m) ^ N = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hprim.pow_eq_one,
      _root_.one_zpow]
  rw [geom_sum_eq hne, hN1]
  simp

/-- Cosine sums over the grid. -/
theorem eqGrid_cos_sum (L : ℕ) (x₀ : ℝ) (m : ℤ) (hm : m ≠ 0) (hm' : |m| ≤ 2 * L) :
    ∑ k : Fin (2 * L + 1), Real.cos (m * eqGrid L x₀ k) = 0 := by
  have h := congrArg Complex.re (eqGrid_exp_sum L x₀ m hm hm')
  rw [Complex.re_sum, Complex.zero_re] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Complex.I * (m : ℂ) * (eqGrid L x₀ k : ℂ) = ((m * eqGrid L x₀ k : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-- Sine sums over the grid. -/
theorem eqGrid_sin_sum (L : ℕ) (x₀ : ℝ) (m : ℤ) (hm' : |m| ≤ 2 * L) :
    ∑ k : Fin (2 * L + 1), Real.sin (m * eqGrid L x₀ k) = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  have h := congrArg Complex.im (eqGrid_exp_sum L x₀ m hm hm')
  rw [Complex.im_sum, Complex.zero_im] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Complex.I * (m : ℂ) * (eqGrid L x₀ k : ℂ) = ((m * eqGrid L x₀ k : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I_im]

/-- The three kinds of columns of the design matrix. -/
theorem fin_design_cases (L : ℕ) (r : Fin (2 * L + 1)) :
    (r : ℕ) = 0 ∨ (∃ p : ℕ, 1 ≤ p ∧ p ≤ L ∧ (r : ℕ) = 2 * p - 1) ∨
      (∃ q : ℕ, 1 ≤ q ∧ q ≤ L ∧ (r : ℕ) = 2 * q) := by
  have := r.isLt
  rcases Nat.even_or_odd' (r : ℕ) with ⟨q, hq | hq⟩
  · by_cases h0 : q = 0
    · left; omega
    · right; right; exact ⟨q, by omega, by omega, hq⟩
  · right; left; exact ⟨q + 1, by omega, by omega, by omega⟩

theorem designMatrix_zero_col (L : ℕ) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (r : Fin (2 * L + 1))
    (hr : (r : ℕ) = 0) : designMatrix L x i r = 1 := by
  simp [designMatrix, hr]

theorem designMatrix_cos_col (L : ℕ) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (r : Fin (2 * L + 1)) (p : ℕ)
    (hp : 1 ≤ p) (hr : (r : ℕ) = 2 * p - 1) : designMatrix L x i r = 2 * Real.cos ((p : ℤ) * x i) := by
  have h1 : (r : ℕ) ≠ 0 := by omega
  have h2 : (r : ℕ) % 2 = 1 := by omega
  have h3 : ((r : ℕ) + 1) / 2 = p := by omega
  simp [designMatrix, h1, h2, h3]

theorem designMatrix_sin_col (L : ℕ) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (r : Fin (2 * L + 1)) (q : ℕ)
    (hq : 1 ≤ q) (hr : (r : ℕ) = 2 * q) : designMatrix L x i r = -2 * Real.sin ((q : ℤ) * x i) := by
  have h1 : (r : ℕ) ≠ 0 := by omega
  have h2 : ¬ (r : ℕ) % 2 = 1 := by omega
  have h3 : (r : ℕ) / 2 = q := by omega
  simp [designMatrix, h1, h2, h3]

/-- On `2L+1` equispaced points `BᵀB = diag(n, 2n, …, 2n)` with `n = 2L+1`. -/
theorem design_gram_eqGrid (L : ℕ) (x₀ : ℝ) :
    (designMatrix L (eqGrid L x₀))ᵀ * designMatrix L (eqGrid L x₀) =
      Matrix.diagonal (fun r : Fin (2 * L + 1) =>
        if (r : ℕ) = 0 then (2 * L + 1 : ℝ) else 2 * (2 * L + 1 : ℝ)) := by
  set X := eqGrid L x₀ with hX
  set N : ℝ := 2 * L + 1 with hN
  have hC0 : ∑ k : Fin (2 * L + 1), Real.cos (((0 : ℤ) : ℝ) * X k) = N := by
    simp [hN]
  have hcc : ∀ a b : ℤ, ∑ k : Fin (2 * L + 1), 2 * Real.cos (a * X k) * (2 * Real.cos (b * X k)) =
      2 * ∑ k : Fin (2 * L + 1), Real.cos (((a - b : ℤ) : ℝ) * X k) +
        2 * ∑ k : Fin (2 * L + 1), Real.cos (((a + b : ℤ) : ℝ) * X k) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  have hss : ∀ a b : ℤ, ∑ k : Fin (2 * L + 1), -2 * Real.sin (a * X k) * (-2 * Real.sin (b * X k)) =
      2 * ∑ k : Fin (2 * L + 1), Real.cos (((a - b : ℤ) : ℝ) * X k) -
        2 * ∑ k : Fin (2 * L + 1), Real.cos (((a + b : ℤ) : ℝ) * X k) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  have hcs : ∀ a b : ℤ, ∑ k : Fin (2 * L + 1), 2 * Real.cos (a * X k) * (-2 * Real.sin (b * X k)) =
      -2 * ∑ k : Fin (2 * L + 1), Real.sin (((a + b : ℤ) : ℝ) * X k) -
        2 * ∑ k : Fin (2 * L + 1), Real.sin (((b - a : ℤ) : ℝ) * X k) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]; ring
  have hsc : ∀ a b : ℤ, ∑ k : Fin (2 * L + 1), -2 * Real.sin (a * X k) * (2 * Real.cos (b * X k)) =
      -2 * ∑ k : Fin (2 * L + 1), Real.sin (((b + a : ℤ) : ℝ) * X k) -
        2 * ∑ k : Fin (2 * L + 1), Real.sin (((a - b : ℤ) : ℝ) * X k) := by
    intro a b
    rw [← hcs b a]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hc1 : ∀ a : ℤ, ∑ k : Fin (2 * L + 1), 2 * Real.cos (a * X k) =
      2 * ∑ k : Fin (2 * L + 1), Real.cos (a * X k) := fun a => by rw [Finset.mul_sum]
  have hs1 : ∀ a : ℤ, ∑ k : Fin (2 * L + 1), -2 * Real.sin (a * X k) =
      -2 * ∑ k : Fin (2 * L + 1), Real.sin (a * X k) := fun a => by rw [Finset.mul_sum]
  have hcos0 : ∀ m : ℤ, m ≠ 0 → |m| ≤ 2 * L → ∑ k : Fin (2 * L + 1), Real.cos (m * X k) = 0 :=
    fun m hm hm' => eqGrid_cos_sum L x₀ m hm hm'
  have hsin0 : ∀ m : ℤ, |m| ≤ 2 * L → ∑ k : Fin (2 * L + 1), Real.sin (m * X k) = 0 :=
    fun m hm' => eqGrid_sin_sum L x₀ m hm'
  ext r s
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply]
  rcases fin_design_cases L r with hr | ⟨p, hp1, hpL, hr⟩ | ⟨p, hp1, hpL, hr⟩ <;>
  rcases fin_design_cases L s with hs | ⟨q, hq1, hqL, hs⟩ | ⟨q, hq1, hqL, hs⟩
  · have hR : ∀ k, designMatrix L X k r = 1 := fun k => designMatrix_zero_col L X k r hr
    have hS : ∀ k, designMatrix L X k s = 1 := fun k => designMatrix_zero_col L X k s hs
    simp only [hR, hS, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      if_pos (Fin.ext (hr.trans hs.symm)), if_pos hr]
    push_cast; ring
  · have hR : ∀ k, designMatrix L X k r = 1 := fun k => designMatrix_zero_col L X k r hr
    have hS : ∀ k, designMatrix L X k s = 2 * Real.cos ((q : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k s q hq1 hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, one_mul, if_neg hne, hc1]
    rw [hcos0 q (by omega) (by rw [abs_of_nonneg (by omega)]; omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = 1 := fun k => designMatrix_zero_col L X k r hr
    have hS : ∀ k, designMatrix L X k s = -2 * Real.sin ((q : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k s q hq1 hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, one_mul, if_neg hne, hs1]
    rw [hsin0 q (by rw [abs_of_nonneg (by omega)]; omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = 2 * Real.cos ((p : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = 1 := fun k => designMatrix_zero_col L X k s hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, mul_one, if_neg hne, hc1]
    rw [hcos0 p (by omega) (by rw [abs_of_nonneg (by omega)]; omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = 2 * Real.cos ((p : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = 2 * Real.cos ((q : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k s q hq1 hs
    simp only [hR, hS, hcc]
    rw [hcos0 ((p : ℤ) + q) (by omega) (by rw [abs_of_nonneg (by omega)]; omega)]
    by_cases hpq : p = q
    · subst hpq
      have hrs : r = s := Fin.ext (hr.trans hs.symm)
      rw [if_pos hrs, if_neg (by omega), sub_self, hC0]; ring
    · have hne : r ≠ s := fun h => by rw [h] at hr; omega
      rw [if_neg hne, hcos0 ((p : ℤ) - q) (by omega) (by rw [abs_le]; constructor <;> omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = 2 * Real.cos ((p : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = -2 * Real.sin ((q : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k s q hq1 hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, hcs, if_neg hne]
    rw [hsin0 ((p : ℤ) + q) (by rw [abs_of_nonneg (by omega)]; omega),
      hsin0 ((q : ℤ) - p) (by rw [abs_le]; constructor <;> omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = -2 * Real.sin ((p : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = 1 := fun k => designMatrix_zero_col L X k s hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, mul_one, if_neg hne, hs1]
    rw [hsin0 p (by rw [abs_of_nonneg (by omega)]; omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = -2 * Real.sin ((p : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = 2 * Real.cos ((q : ℤ) * X k) :=
      fun k => designMatrix_cos_col L X k s q hq1 hs
    have hne : r ≠ s := fun h => by rw [h] at hr; omega
    simp only [hR, hS, hsc, if_neg hne]
    rw [hsin0 ((q : ℤ) + p) (by rw [abs_of_nonneg (by omega)]; omega),
      hsin0 ((p : ℤ) - q) (by rw [abs_le]; constructor <;> omega)]; ring
  · have hR : ∀ k, designMatrix L X k r = -2 * Real.sin ((p : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k r p hp1 hr
    have hS : ∀ k, designMatrix L X k s = -2 * Real.sin ((q : ℤ) * X k) :=
      fun k => designMatrix_sin_col L X k s q hq1 hs
    simp only [hR, hS, hss]
    rw [hcos0 ((p : ℤ) + q) (by omega) (by rw [abs_of_nonneg (by omega)]; omega)]
    by_cases hpq : p = q
    · subst hpq
      have hrs : r = s := Fin.ext (hr.trans hs.symm)
      rw [if_pos hrs, if_neg (by omega), sub_self, hC0]; ring
    · have hne : r ≠ s := fun h => by rw [h] at hr; omega
      rw [if_neg hne, hcos0 ((p : ℤ) - q) (by omega) (by rw [abs_le]; constructor <;> omega)]; ring

/-! ### Tools: design form, coefficient extraction, invertibility on the grid -/

/-- Fourier coefficients of a real trigonometric polynomial. -/
theorem realFourierCoeff_of_trig (L : ℕ) (c : ℤ → ℂ) (g : ℝ → ℝ) (hg : ∀ x, ((g x : ℝ) : ℂ) = trig L c x)
    (m : ℤ) (hm : m ∈ Finset.Icc (-(L : ℤ)) L) : realFourierCoeff g m = c m := by
  unfold realFourierCoeff
  simp_rw [hg, trig]
  rw [fourier_coeff_sum, if_pos hm]

/-- A real trigonometric polynomial is the design row applied to its real coefficient vector. -/
theorem design_form_of_trig (L : ℕ) (c : ℤ → ℂ) (hc : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0)
    (g : ℝ → ℝ) (hg : ∀ x, ((g x : ℝ) : ℂ) = trig L c x) (x : ℝ) :
    g x = ∑ r, designEntry L x r * realRep L (realFourierCoeff g) r := by
  have h := congrFun (real_trig_eq_design L c hc g hg (fun _ : Fin 1 => x)) 0
  rw [realRep_congr L (realFourierCoeff g) c (realFourierCoeff_of_trig L c g hg)]
  simpa [mulVec, dotProduct, designEntry] using h

/-- Extension of a vector on `Fin (2L+1)` by zero. -/
def vecExt (L : ℕ) (v : Fin (2 * L + 1) → ℝ) (r : ℕ) : ℝ :=
  if h : r < 2 * L + 1 then v ⟨r, h⟩ else 0

/-- Complex coefficients of the real trigonometric polynomial with real coefficient vector `v`. -/
def unRealRep (L : ℕ) (v : Fin (2 * L + 1) → ℝ) (k : ℤ) : ℂ :=
  if k = 0 then (vecExt L v 0 : ℂ)
  else if 0 < k ∧ k ≤ L then ⟨vecExt L v (2 * k.toNat - 1), vecExt L v (2 * k.toNat)⟩
  else if -(L : ℤ) ≤ k ∧ k < 0 then ⟨vecExt L v (2 * (-k).toNat - 1), -vecExt L v (2 * (-k).toNat)⟩
  else 0

theorem unRealRep_supp (L : ℕ) (v : Fin (2 * L + 1) → ℝ) :
    ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → unRealRep L v k = 0 := by
  intro k hk
  simp only [Finset.mem_Icc] at hk
  unfold unRealRep
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem unRealRep_symm (L : ℕ) (v : Fin (2 * L + 1) → ℝ) (k : ℤ) :
    unRealRep L v (-k) = (starRingEnd ℂ) (unRealRep L v k) := by
  unfold unRealRep
  by_cases h0 : k = 0
  · subst h0; simp
  by_cases h1 : 0 < k ∧ k ≤ L
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg h0, if_pos h1, neg_neg]
    apply Complex.ext <;> simp
  by_cases h2 : -(L : ℤ) ≤ k ∧ k < 0
  · rw [if_neg (by omega), if_pos (by omega), if_neg h0, if_neg h1, if_pos h2]
    apply Complex.ext <;> simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1, if_neg h2, map_zero]

theorem realRep_unRealRep (L : ℕ) (v : Fin (2 * L + 1) → ℝ) : realRep L (unRealRep L v) = v := by
  funext r
  have hv : ∀ n (h : n = (r : ℕ)), vecExt L v n = v r := by
    intro n h
    subst h
    simp [vecExt, r.isLt]
  unfold realRep
  rcases fin_design_cases L r with hr | ⟨p, hp1, hpL, hr⟩ | ⟨q, hq1, hqL, hr⟩
  · rw [if_pos hr]
    simp [unRealRep, hv 0 hr.symm]
  · have h1 : (r : ℕ) ≠ 0 := by omega
    have h2 : (r : ℕ) % 2 = 1 := by omega
    have h3 : ((r : ℕ) + 1) / 2 = p := by omega
    rw [if_neg h1, if_pos h2, h3]
    unfold unRealRep
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [Int.toNat_natCast]
    exact hv _ (by omega)
  · have h1 : (r : ℕ) ≠ 0 := by omega
    have h2 : ¬ (r : ℕ) % 2 = 1 := by omega
    have h3 : (r : ℕ) / 2 = q := by omega
    rw [if_neg h1, if_neg h2, h3]
    unfold unRealRep
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [Int.toNat_natCast]
    exact hv _ (by omega)

/-- The design form `x ↦ Σ_r B_r(x) v_r` is the trigonometric polynomial with coefficients `unRealRep L v`. -/
theorem design_eq_trig (L : ℕ) (v : Fin (2 * L + 1) → ℝ) (x : ℝ) :
    (((∑ r, designEntry L x r * v r : ℝ)) : ℂ) = trig L (unRealRep L v) x := by
  have hreal : ∀ x, (((trig L (unRealRep L v) x).re : ℝ) : ℂ) = trig L (unRealRep L v) x := by
    intro x
    have h := trig_conj L (unRealRep L v) x
    have hc : (fun k => (starRingEnd ℂ) (unRealRep L v (-k))) = unRealRep L v := by
      funext k
      rw [unRealRep_symm, Complex.conj_conj]
    rw [hc] at h
    exact Complex.conj_eq_iff_re.mp h
  have h := congrFun (real_trig_eq_design L (unRealRep L v) (unRealRep_supp L v)
    (fun x => (trig L (unRealRep L v) x).re) hreal (fun _ : Fin 1 => x)) 0
  rw [realRep_unRealRep] at h
  rw [← hreal x]
  congr 1
  rw [h]
  simp [mulVec, dotProduct, designEntry]

/-- The real Fourier coefficient vector of the design form `Σ_r B_r v_r` is `v`. -/
theorem realRep_realFourierCoeff_design (L : ℕ) (v : Fin (2 * L + 1) → ℝ) :
    realRep L (realFourierCoeff (fun x => ∑ r, designEntry L x r * v r)) = v := by
  rw [realRep_congr L _ (unRealRep L v)
    (realFourierCoeff_of_trig L (unRealRep L v) _ (design_eq_trig L v)), realRep_unRealRep]

/-- The design matrix on the equispaced grid is invertible. -/
theorem design_det_ne_zero (L : ℕ) (x₀ : ℝ) : (designMatrix L (eqGrid L x₀)).det ≠ 0 := by
  have h := congrArg Matrix.det (design_gram_eqGrid L x₀)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
  intro h0
  rw [h0, mul_zero] at h
  refine (Finset.prod_ne_zero_iff.2 fun r _ => ?_) h.symm
  split_ifs <;> positivity

/-- A vector is recovered from the values of its design form on the grid. -/
theorem vec_eq_design_inv (L : ℕ) (x₀ : ℝ) (v : Fin (2 * L + 1) → ℝ) :
    v = (designMatrix L (eqGrid L x₀))⁻¹ *ᵥ (fun k => ∑ r, designEntry L (eqGrid L x₀ k) r * v r) := by
  have hB : IsUnit (designMatrix L (eqGrid L x₀)).det := isUnit_iff_ne_zero.2 (design_det_ne_zero L x₀)
  have : (fun k => ∑ r, designEntry L (eqGrid L x₀ k) r * v r) = designMatrix L (eqGrid L x₀) *ᵥ v := by
    funext k
    simp [mulVec, dotProduct, designEntry, designMatrix]
  rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]

end

end


/-! # Section 14: Lemma 4.1 (polynomial structure) -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 14. Lemma 4.1 (polynomial structure), for any circuit of Definition 3.1 -/

/-- State `W_L S(x) W_{L−1} ⋯ S(x) W_0 e` of a general circuit on `n`. -/
def genState {n : Type*} [Fintype n] [DecidableEq n] :
    (L : ℕ) → (ℝ → Matrix n n ℂ) → (Fin (L + 1) → Matrix n n ℂ) → (n → ℂ) → ℝ → n → ℂ
  | 0, _, W, e, _ => W 0 *ᵥ e
  | L + 1, S, W, e, x => W (Fin.last (L + 1)) *ᵥ (S x *ᵥ genState L S (fun i => W (Fin.castSucc i)) e x)

/-- Output `Re ⟨ψ, M ψ⟩` (equal to `⟨ψ, M ψ⟩` for Hermitian `M`). -/
def genModel {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (S : ℝ → Matrix n n ℂ) (M : Matrix n n ℂ)
    (e : n → ℂ) (W : Fin (L + 1) → Matrix n n ℂ) (x : ℝ) : ℝ :=
  (dotProduct (star (genState L S W e x)) (M *ᵥ genState L S W e x)).re

/-- Path expansion of the state of a general circuit: each amplitude is a sum over index paths of one entry of every
    block times a block-independent continuous function of `x`. -/
theorem genState_paths {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (S : ℝ → Matrix n n ℂ)
    (hS : Continuous S) (e : n → ℂ) :
    ∃ σ : (Fin (L + 1) → n × n) → n → ℝ → ℂ, (∀ p b, Continuous (σ p b)) ∧
      ∀ W x b, genState L S W e x b = ∑ p, (∏ ℓ, W ℓ (p ℓ).1 (p ℓ).2) * σ p b x := by
  induction L with
  | zero =>
    refine ⟨fun p b _ => if (p 0).1 = b then e (p 0).2 else 0, fun p b => continuous_const, ?_⟩
    intro W x b
    rw [← (Equiv.funUnique (Fin 1) (n × n)).symm.sum_comp, Fintype.sum_prod_type]
    simp [genState, mulVec, dotProduct]
  | succ L ih =>
    obtain ⟨σ, hσc, hσ⟩ := ih
    refine ⟨fun p b x => if (p (Fin.last (L + 1))).1 = b then
      ∑ d, S x (p (Fin.last (L + 1))).2 d * σ (Fin.init p) d x else 0, ?_, ?_⟩
    · intro p b
      dsimp only
      split_ifs
      · refine continuous_finset_sum _ fun d _ => ?_
        exact ((continuous_apply d).comp ((continuous_apply _).comp hS)).mul (hσc _ _)
      · exact continuous_const
    · intro W x b
      rw [← (Fin.snocEquiv (fun _ => n × n)).sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
      have hsn : ∀ f : (n × n) × (Fin (L + 1) → n × n),
          Fin.snocEquiv (fun _ => n × n) f = Fin.snoc f.2 f.1 := fun f => by
        funext i; simp [Fin.snocEquiv_apply]
      simp only [hsn, Fin.prod_univ_castSucc (n := L + 1), Fin.snoc_last, Fin.snoc_castSucc, Fin.init_snoc]
      simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true, genState, mulVec, dotProduct, hσ]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun d _ => ?_
      ring
/-- **Lemma 4.1.** Every Fourier coefficient is a sum over index paths of a block-independent coefficient times
    one entry of every block and one conjugated entry of every block. Hence it is a polynomial of total degree
    ≤ 2(L+1) in the entries and their conjugates, of degree ≤ 2 in each block, and every monomial contains entries of
    all L+1 blocks. -/
theorem coupling_depth {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (S : ℝ → Matrix n n ℂ)
    (hS : Continuous S) (M : Matrix n n ℂ) (e : n → ℂ) (ω : ℤ) :
    ∃ κ : (Fin (L + 1) → n × n) → (Fin (L + 1) → n × n) → ℂ, ∀ W : Fin (L + 1) → Matrix n n ℂ,
      realFourierCoeff (genModel L S M e W) ω =
        ∑ p, ∑ p', κ p p' * (∏ ℓ, W ℓ (p ℓ).1 (p ℓ).2) * ∏ ℓ, (starRingEnd ℂ) (W ℓ (p' ℓ).1 (p' ℓ).2) := by
  obtain ⟨σ, hσc, hσ⟩ := genState_paths L S hS e
  set A : (Fin (L + 1) → Matrix n n ℂ) → (Fin (L + 1) → n × n) → ℂ :=
    fun W p => ∏ ℓ, W ℓ (p ℓ).1 (p ℓ).2 with hA
  set Bc : (Fin (L + 1) → Matrix n n ℂ) → (Fin (L + 1) → n × n) → ℂ :=
    fun W p => ∏ ℓ, (starRingEnd ℂ) (W ℓ (p ℓ).1 (p ℓ).2) with hBc
  set τ : (Fin (L + 1) → n × n) → (Fin (L + 1) → n × n) → ℝ → ℂ :=
    fun p p' x => ∑ b, ∑ c, (starRingEnd ℂ) (σ p' b x) * M b c * σ p c x with hτ
  set ρ : (Fin (L + 1) → n × n) → (Fin (L + 1) → n × n) → ℝ → ℂ :=
    fun p p' x => (τ p p' x + (starRingEnd ℂ) (τ p' p x)) / 2 with hρ
  have hτc : ∀ p p', Continuous (τ p p') := by
    intro p p'
    refine continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ => ?_
    exact ((Complex.continuous_conj.comp (hσc p' b)).mul continuous_const).mul (hσc p c)
  have hρc : ∀ p p', Continuous (ρ p p') := fun p p' =>
    ((hτc p p').add (Complex.continuous_conj.comp (hτc p' p))).div_const _
  have hconjA : ∀ W p, (starRingEnd ℂ) (A W p) = Bc W p := fun W p => by simp [hA, hBc, map_prod]
  have hconjB : ∀ W p, (starRingEnd ℂ) (Bc W p) = A W p := fun W p => by simp [hA, hBc, map_prod]
  have hz : ∀ W x, dotProduct (star (genState L S W e x)) (M *ᵥ genState L S W e x) =
      ∑ p, ∑ p', A W p * Bc W p' * τ p p' x := by
    intro W x
    have h1 : ∀ b, (star (genState L S W e x)) b = ∑ p', Bc W p' * (starRingEnd ℂ) (σ p' b x) := by
      intro b
      rw [Pi.star_apply, hσ, star_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [star_mul', ← hconjA]
      simp only [hA, Complex.star_def]
    have h2 : ∀ b, (M *ᵥ genState L S W e x) b = ∑ p, A W p * ∑ c, M b c * σ p c x := by
      intro b
      simp only [mulVec, dotProduct, hσ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [hA]; ring
    simp only [dotProduct, h1, h2, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun p' _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    simp only [hτ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have hkey : ∀ W x, ((genModel L S M e W x : ℝ) : ℂ) = ∑ p, ∑ p', A W p * Bc W p' * ρ p p' x := by
    intro W x
    unfold genModel
    rw [Complex.re_eq_add_conj, hz]
    simp only [map_sum, map_mul, hconjA, hconjB]
    have hc : ∑ p, ∑ p', Bc W p * A W p' * (starRingEnd ℂ) (τ p p' x) =
        ∑ p, ∑ p', A W p * Bc W p' * (starRingEnd ℂ) (τ p' p x) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by ring
    rw [hc, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p' _ => ?_
    simp only [hρ]
    ring
  refine ⟨fun p p' => (1 / (2 * Real.pi) : ℂ) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    ρ p p' x * Complex.exp (-(Complex.I * (ω : ℂ) * (x : ℂ))), fun W => ?_⟩
  have hcont : ∀ p p', Continuous (fun x : ℝ => A W p * Bc W p' * ρ p p' x *
      Complex.exp (-(Complex.I * (ω : ℂ) * (x : ℂ)))) := fun p p' =>
    (continuous_const.mul (hρc p p')).mul (by fun_prop)
  have hint : ∀ p p', ∫ x in (0 : ℝ)..(2 * Real.pi), A W p * Bc W p' * ρ p p' x *
      Complex.exp (-(Complex.I * (ω : ℂ) * (x : ℂ))) = A W p * Bc W p' * ∫ x in (0 : ℝ)..(2 * Real.pi),
        ρ p p' x * Complex.exp (-(Complex.I * (ω : ℂ) * (x : ℂ))) := by
    intro p p'
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  unfold realFourierCoeff
  simp_rw [hkey W, Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    (continuous_finset_sum _ fun p' _ => hcont p p').intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [intervalIntegral.integral_finset_sum (fun p' _ => (hcont p p').intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [hint]
  simp only [hA, hBc]
  ring

end

end


/-! # Section 15: the serial circuit at the level of gates (Lemma 4.2, Definition 3.2, Eq. (2)) -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 15. The serial circuit at the level of gates -/

/-- Product `V_{t−1} ⋯ V_0` of the gates of a block (gate 0 acts first). -/
def blockProd {n : Type*} [Fintype n] [DecidableEq n] : (t : ℕ) → (Fin t → Matrix n n ℂ) → Matrix n n ℂ
  | 0, _ => 1
  | t + 1, g => g (Fin.last t) * blockProd t (fun i => g (Fin.castSucc i))

/-- Gates of a circuit with `L+1` blocks of `tbl` gates. -/
abbrev Gates (L tbl : ℕ) (n : Type*) := Fin (L + 1) × Fin tbl → Matrix n n ℂ

/-- All gates lie in SU(n). -/
def InSU {L tbl : ℕ} {n : Type*} [Fintype n] [DecidableEq n] (G : Gates L tbl n) : Prop :=
  ∀ i, G i ∈ Matrix.specialUnitaryGroup n ℂ

/-- Replace gate `i` by `A`. -/
def perturb {L tbl : ℕ} {n : Type*} (G : Gates L tbl n) (i : Fin (L + 1) × Fin tbl) (A : Matrix n n ℂ) :
    Gates L tbl n :=
  Function.update G i A

def gateState (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (x : ℝ) : Fin 2 → ℂ :=
  serialState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x

/-- Serial output `⟨ψ, Zψ⟩`. -/
def gateModel (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (x : ℝ) : ℝ :=
  (ip (gateState L tbl G x) (Zm *ᵥ gateState L tbl G x)).re

/-- Tangent vector of the state when gate `i` moves along the curve `γ`. -/
def gateTangent (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) : Fin 2 → ℂ :=
  deriv (fun s => gateState L tbl (perturb G i (γ s)) x) 0

/-- `h_j = ⟨Tψ, ∂_jψ⟩`. -/
def gateH (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl) (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ℝ) : ℂ :=
  ip (T (gateState L tbl G x)) (gateTangent L tbl G i γ x)

/-- `μ = ⟨Tψ, Zψ⟩`. -/
def gateMu (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (x : ℝ) : ℂ :=
  ip (T (gateState L tbl G x)) (Zm *ᵥ gateState L tbl G x)

/-- A product of gates in a submonoid lies in the submonoid. -/
theorem blockProd_mem {n : Type*} [Fintype n] [DecidableEq n] (S : Submonoid (Matrix n n ℂ)) :
    ∀ (t : ℕ) (g : Fin t → Matrix n n ℂ), (∀ j, g j ∈ S) → blockProd t g ∈ S
  | 0, _, _ => S.one_mem
  | t + 1, _, h => S.mul_mem (h _) (blockProd_mem S t _ fun _ => h _)

/-- A block with one gate replaced: `blockProd t (update g k A) = U * A * D`, where `D` is determined by the
    gates before `k` and `U` is a product of the gates after `k`. -/
theorem blockProd_split {n : Type*} [Fintype n] [DecidableEq n] (S : Submonoid (Matrix n n ℂ)) :
    ∀ (t : ℕ) (g : Fin t → Matrix n n ℂ) (k : Fin t), ∃ D : Matrix n n ℂ,
      ∀ g' : Fin t → Matrix n n ℂ, (∀ j, j < k → g' j = g j) → ∃ U : Matrix n n ℂ,
        (∀ A, blockProd t (Function.update g' k A) = U * A * D) ∧ ((∀ j, k < j → g' j ∈ S) → U ∈ S)
  | 0, _, k => k.elim0
  | t + 1, g, k => by
    by_cases hk : k = Fin.last t
    · subst hk
      refine ⟨blockProd t (fun i => g (Fin.castSucc i)), fun g' hg' => ⟨1, fun A => ?_, fun _ => S.one_mem⟩⟩
      simp only [blockProd, Function.update_self, one_mul]
      congr 1
      congr 1
      funext i
      rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne, hg' _ (Fin.castSucc_lt_last i)]
    · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      obtain ⟨D, hD⟩ := blockProd_split S t (fun i => g (Fin.castSucc i)) k'
      refine ⟨D, fun g' hg' => ?_⟩
      obtain ⟨U, hU, hUS⟩ := hD (fun i => g' (Fin.castSucc i))
        (fun j hj => hg' _ (Fin.castSucc_lt_castSucc_iff.mpr hj))
      refine ⟨g' (Fin.last t) * U, fun A => ?_, fun hS => S.mul_mem (hS _ (Fin.castSucc_lt_last k'))
        (hUS fun j hj => hS _ (Fin.castSucc_lt_castSucc_iff.mpr hj))⟩
      have hc : (fun i => Function.update g' (Fin.castSucc k') A (Fin.castSucc i)) =
          Function.update (fun i => g' (Fin.castSucc i)) k' A :=
        Function.update_comp_eq_of_injective g' (Fin.castSucc_injective _) k' A
      simp only [blockProd]
      rw [Function.update_of_ne (Fin.castSucc_lt_last k').ne', hc, hU]
      simp only [Matrix.mul_assoc]

/-- A serial state with one block replaced: `serialState L (update V ℓ M) x = Down x (M (Pre x))`, where `Pre` is
    determined by the blocks before `ℓ` and `Down x` is a product of `R_X(x)` and the blocks after `ℓ`. -/
theorem serialState_split :
    ∀ (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : Fin (L + 1)), ∃ Pre : ℝ → Fin 2 → ℂ,
      ∀ V' : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ, (∀ j, j < ℓ → V' j = V j) →
        ∃ Down : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
          (∀ M x, serialState L (Function.update V' ℓ M) x = Down x *ᵥ (M *ᵥ Pre x)) ∧
          ((∀ j, ℓ < j → V' j ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) →
            ∀ x, Down x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
  | 0, V, ℓ => by
    obtain rfl : ℓ = 0 := Fin.fin_one_eq_zero ℓ
    refine ⟨fun _ => ![1, 0], fun V' _ => ⟨fun _ => 1, fun M x => ?_, fun _ _ => one_mem _⟩⟩
    simp [serialState]
  | L + 1, V, ℓ => by
    by_cases hℓ : ℓ = Fin.last (L + 1)
    · subst hℓ
      refine ⟨fun x => RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x, fun V' hV' =>
        ⟨fun _ => 1, fun M x => ?_, fun _ _ => one_mem _⟩⟩
      simp only [serialState, Function.update_self, Matrix.one_mulVec]
      congr 2
      congr 1
      funext i
      rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne, hV' _ (Fin.castSucc_lt_last i)]
    · obtain ⟨ℓ', rfl⟩ := Fin.exists_castSucc_eq.mpr hℓ
      obtain ⟨Pre, hPre⟩ := serialState_split L (fun i => V (Fin.castSucc i)) ℓ'
      refine ⟨Pre, fun V' hV' => ?_⟩
      obtain ⟨Down, hDown, hDS⟩ := hPre (fun i => V' (Fin.castSucc i))
        (fun j hj => hV' _ (Fin.castSucc_lt_castSucc_iff.mpr hj))
      refine ⟨fun x => V' (Fin.last (L + 1)) * RXm x * Down x, fun M x => ?_, fun hS x =>
        mul_mem (mul_mem (hS _ (Fin.castSucc_lt_last ℓ')) (RXm_mem_SU2 x))
          (hDS (fun j hj => hS _ (Fin.castSucc_lt_castSucc_iff.mpr hj)) x)⟩
      have hc : (fun i => Function.update V' (Fin.castSucc ℓ') M (Fin.castSucc i)) =
          Function.update (fun i => V' (Fin.castSucc i)) ℓ' M :=
        Function.update_comp_eq_of_injective V' (Fin.castSucc_injective _) ℓ' M
      simp only [serialState]
      rw [Function.update_of_ne (Fin.castSucc_lt_last ℓ').ne', hc, hDown]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Gates strictly before gate `i` in circuit order. -/
def GateBefore {L tbl : ℕ} (i' i : Fin (L + 1) × Fin tbl) : Prop :=
  i'.1 < i.1 ∨ (i'.1 = i.1 ∧ i'.2 < i.2)

/-- The gate-level split: replacing gate `i` by `A` gives `Dn x (A (φ x))`, with `φ` determined by the gates
    before `i` and `Dn x ∈ SU(2)` a product of later gates and encodings. -/
theorem gate_split (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl) :
    ∃ φ : ℝ → Fin 2 → ℂ, ∀ G' : Gates L tbl (Fin 2), (∀ i', GateBefore i' i → G' i' = G i') →
      ∃ Dn : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ A x, gateState L tbl (perturb G' i A) x = Dn x *ᵥ (A *ᵥ φ x)) ∧
        (InSU G' → ∀ x, Dn x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  obtain ⟨D, hD⟩ := blockProd_split (Matrix.specialUnitaryGroup (Fin 2) ℂ) tbl
    (fun g => G (i.1, g)) i.2
  obtain ⟨Pre, hPre⟩ := serialState_split L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) i.1
  refine ⟨fun x => D *ᵥ Pre x, fun G' hG' => ?_⟩
  obtain ⟨U, hU, hUS⟩ := hD (fun g => G' (i.1, g)) (fun j hj => hG' (i.1, j) (Or.inr ⟨rfl, hj⟩))
  obtain ⟨Down, hDown, hDS⟩ := hPre (fun ℓ => blockProd tbl (fun g => G' (ℓ, g)))
    (fun j hj => by
      show blockProd tbl (fun g => G' (j, g)) = blockProd tbl (fun g => G (j, g))
      congr 1
      funext g
      exact hG' (j, g) (Or.inl hj))
  refine ⟨fun x => Down x * U, fun A x => ?_, fun hS x => mul_mem (hDS (fun j _ => ?_) x) (hUS fun j _ => hS _)⟩
  · have hblocks : (fun ℓ => blockProd tbl (fun g => perturb G' i A (ℓ, g))) =
        Function.update (fun ℓ => blockProd tbl (fun g => G' (ℓ, g))) i.1 (U * A * D) := by
      funext ℓ
      by_cases hℓ : ℓ = i.1
      · subst hℓ
        rw [Function.update_self, ← hU A]
        congr 1
        funext g
        by_cases hg : g = i.2
        · subst hg; simp [perturb]
        · rw [Function.update_of_ne hg]
          simp only [perturb]
          rw [Function.update_of_ne (fun h => hg (congrArg Prod.snd h))]
      · rw [Function.update_of_ne hℓ]
        congr 1
        funext g
        simp only [perturb]
        rw [Function.update_of_ne (fun h => hℓ (congrArg Prod.fst h))]
    unfold gateState
    rw [hblocks, hDown]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · exact blockProd_mem (Matrix.specialUnitaryGroup (Fin 2) ℂ) tbl _ fun g => hS _

/-- The blocks of a circuit with gate `i` replaced by `A`: only block `i.1` changes, to `U * A * D`. -/
theorem gate_blocks_update {L tbl : ℕ} {n : Type*} [Fintype n] [DecidableEq n] (G : Gates L tbl n)
    (i : Fin (L + 1) × Fin tbl) :
    ∃ U D : Matrix n n ℂ, (InSU G → U ∈ Matrix.specialUnitaryGroup n ℂ) ∧
      (InSU G → D ∈ Matrix.specialUnitaryGroup n ℂ) ∧ ∀ A,
      (fun ℓ => blockProd tbl (fun g => perturb G i A (ℓ, g))) =
        Function.update (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) i.1 (U * A * D) := by
  obtain ⟨D, hD⟩ := blockProd_split (Matrix.specialUnitaryGroup n ℂ) tbl (fun g => G (i.1, g)) i.2
  obtain ⟨U, hU, hUS⟩ := hD (fun g => G (i.1, g)) (fun _ _ => rfl)
  have hDS : InSU G → D ∈ Matrix.specialUnitaryGroup n ℂ := by
    intro hG
    have hUs := hUS fun j _ => hG _
    have hB : blockProd tbl (Function.update (fun g => G (i.1, g)) i.2 1) ∈
        Matrix.specialUnitaryGroup n ℂ :=
      blockProd_mem _ tbl _ fun j => by
        by_cases hj : j = i.2
        · subst hj; rw [Function.update_self]; exact one_mem _
        · rw [Function.update_of_ne hj]; exact hG _
    rw [hU 1, mul_one] at hB
    have hU' : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hUs.1
    have hD' : D = star U * (U * D) := by rw [← mul_assoc, hU', one_mul]
    rw [hD']
    have hstar : star U ∈ Matrix.specialUnitaryGroup n ℂ := by
      rw [Matrix.mem_specialUnitaryGroup_iff] at hUs ⊢
      refine ⟨Unitary.star_mem hUs.1, ?_⟩
      rw [show star U = Uᴴ from rfl, Matrix.det_conjTranspose, hUs.2, star_one]
    exact mul_mem hstar hB
  refine ⟨U, D, fun hG => hUS fun j _ => hG _, hDS, fun A => ?_⟩
  funext ℓ
  by_cases hℓ : ℓ = i.1
  · subst hℓ
    rw [Function.update_self, ← hU A]
    congr 1
    funext g
    by_cases hg : g = i.2
    · subst hg; simp [perturb]
    · rw [Function.update_of_ne hg]
      simp only [perturb]
      rw [Function.update_of_ne (fun h => hg (congrArg Prod.snd h))]
  · rw [Function.update_of_ne hℓ]
    congr 1
    funext g
    simp only [perturb]
    rw [Function.update_of_ne (fun h => hℓ (congrArg Prod.fst h))]

/-- The state along a gate curve has derivative `dSerial` with only block `i.1` varying. -/
theorem gate_state_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hγ0 : γ 0 = G i)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) :
    ∃ dV : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ, (∀ ℓ : Fin (L + 1), (i.1 : ℕ) < (ℓ : ℕ) → dV ℓ = 0) ∧
      ∀ x, HasDerivAt (fun s => gateState L tbl (perturb G i (γ s)) x)
        (dSerial L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) dV x) 0 := by
  obtain ⟨U, D, -, -, hUD⟩ := gate_blocks_update G i
  set Vb := fun ℓ => blockProd tbl (fun g => G (ℓ, g)) with hVb
  refine ⟨Function.update 0 i.1 (U * dγ * D), fun ℓ hℓ => ?_, fun x => ?_⟩
  · rw [Function.update_of_ne (fun h => by rw [h] at hℓ; exact lt_irrefl _ hℓ)]; rfl
  · have hcurve : ∀ ℓ a b, HasDerivAt (fun s => Function.update Vb i.1 (U * γ s * D) ℓ a b)
        (Function.update (0 : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) i.1 (U * dγ * D) ℓ a b) 0 := by
      intro ℓ a b
      by_cases hℓ : ℓ = i.1
      · subst hℓ
        simp only [Function.update_self]
        simp only [Matrix.mul_apply]
        apply HasDerivAt.fun_sum; intro c _
        apply HasDerivAt.mul_const
        apply HasDerivAt.fun_sum; intro e _
        exact (hdγ e c).const_mul _
      · simp only [Function.update_of_ne hℓ]
        exact hasDerivAt_const _ _
    have h := serialState_hasDerivAt L (fun s => Function.update Vb i.1 (U * γ s * D)) _ hcurve x
    have h0 : Function.update Vb i.1 (U * γ 0 * D) = Vb := by
      rw [← hUD, hγ0]
      funext ℓ
      simp [perturb, Function.update_eq_self, hVb]
    rw [h0] at h
    unfold gateState
    simp_rw [hUD]
    exact h

/-- A normalised state and any vector: `v − ⟨ψ, v⟩ ψ = ⟨Tψ, v⟩ Tψ`. -/
theorem collinear_of_normalised (ψ v : Fin 2 → ℂ) (hψ : ip ψ ψ = 1) :
    v - ip ψ v • ψ = ip (T ψ) v • T ψ := by
  simp only [ip] at hψ
  funext k
  fin_cases k
  · simp [ip, T]
    linear_combination (-(v 0)) * hψ
  · simp [ip, T]
    linear_combination (-(v 1)) * hψ

/-- Circuits with gates in SU(n), perturbed at one gate by a unitary, have unitary blocks. -/
theorem perturb_blocks_unitary {L tbl : ℕ} {n : Type*} [Fintype n] [DecidableEq n] (G : Gates L tbl n)
    (hG : InSU G) (i : Fin (L + 1) × Fin tbl) (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ)
    (ℓ : Fin (L + 1)) : blockProd tbl (fun g => perturb G i A (ℓ, g)) ∈ Matrix.unitaryGroup n ℂ := by
  apply blockProd_mem (Matrix.unitaryGroup n ℂ)
  intro g
  by_cases h : (ℓ, g) = i
  · rw [h]; simp only [perturb, Function.update_self]; exact hA
  · simp only [perturb, Function.update_of_ne h]; exact (hG _).1

theorem gateState_normalised (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : ∀ i, G i ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (x : ℝ) : ip (gateState L tbl G x) (gateState L tbl G x) = 1 :=
  serialState_normalised L _ (fun _ => blockProd_mem (Matrix.unitaryGroup (Fin 2) ℂ) tbl _
    fun _ => hG _) x

/-- Derivative of `s ↦ D (γ s v)` for fixed `D`, `v`. -/
theorem hasDerivAt_mulVec_mulVec_const (D : Matrix (Fin 2) (Fin 2) ℂ) (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) (v : Fin 2 → ℂ) :
    HasDerivAt (fun s => D *ᵥ (γ s *ᵥ v)) (D *ᵥ (dγ *ᵥ v)) 0 := by
  have h := hasDerivAt_mulVec_curve γ dγ (fun _ => v) 0 hdγ (hasDerivAt_const _ _)
  simp only [Matrix.mulVec_zero, add_zero] at h
  exact hasDerivAt_mulVec D _ _ 0 h

theorem perturb_self {L tbl : ℕ} {n : Type*} (G : Gates L tbl n) (i : Fin (L + 1) × Fin tbl) :
    perturb G i (G i) = G := by
  simp [perturb]

/-- **Lemma 4.2, Eq. (envelope).** For every parameter entering gate `i` through a differentiable curve `γ` of
    unitaries, `∂f = 2 Re[conj(h) μ]` with the same `μ` for all parameters. -/
theorem gate_phase_locking (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hγ : ∀ s, γ s ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hγ0 : γ 0 = G i)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) (x : ℝ) :
    HasDerivAt (fun s => gateModel L tbl (perturb G i (γ s)) x)
      (2 * ((starRingEnd ℂ) (gateH L tbl G i γ x) * gateMu L tbl G x).re) 0 := by
  obtain ⟨dV, -, hd⟩ := gate_state_hasDerivAt L tbl G i γ hγ0 dγ hdγ
  have hd' := hd x
  rw [← show gateTangent L tbl G i γ x = _ from (hd x).deriv] at hd'
  have hnorm : ∀ s, ip (gateState L tbl (perturb G i (γ s)) x) (gateState L tbl (perturb G i (γ s)) x) = 1 :=
    fun s => serialState_normalised L _ (fun ℓ => perturb_blocks_unitary G hG i (γ s) (hγ s) ℓ) x
  have h0 : gateState L tbl (perturb G i (γ 0)) x = gateState L tbl G x := by rw [hγ0, perturb_self]
  have htan := tangent_of_normalised _ _ 0 hnorm hd'
  rw [h0] at htan
  have h := expval_hasDerivAt Zm Zm_hermitian _ _ 0 hd'
  rw [h0, envelope_identity _ _ Zm (gateState_normalised L tbl G (fun i => (hG i).1) x) htan
    Zm_hermitian] at h
  exact h

/-- **Lemma 4.2, collinearity.** `(I − |ψ⟩⟨ψ|) ∂ψ = h · Tψ` for every parameter.
    (The hypotheses `hγ`, `hγ0` and `hdγ` are kept as stated in the paper; the proof does not need them.) -/
theorem gate_tangent_collinear (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (_hγ : ∀ s, γ s ∈ Matrix.unitaryGroup (Fin 2) ℂ) (_hγ0 : γ 0 = G i)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (_hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) (x : ℝ) :
    gateTangent L tbl G i γ x - ip (gateState L tbl G x) (gateTangent L tbl G i γ x) • gateState L tbl G x =
      gateH L tbl G i γ x • T (gateState L tbl G x) := by
  exact collinear_of_normalised _ _ (gateState_normalised L tbl G (fun i => (hG i).1) x)

/-- **Lemma 4.2, degree of μ.** -/
theorem gate_envelope_trig (L tbl : ℕ) (G : Gates L tbl (Fin 2)) :
    ∃ b : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0) ∧ ∀ x, gateMu L tbl G x = trig L b x := by
  exact serialState_pairing_trig L _ Zm

/-- **Lemma 4.2, degree of h.** `h` is a trigonometric polynomial of degree at most the number `i.1` of encoding
    layers preceding the gate.
    (The hypothesis `hγ` is kept as stated in the paper; the proof does not need them.) -/
theorem gate_tangent_trig (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (_hγ : ∀ s, γ s ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hγ0 : γ 0 = G i)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) :
    ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-((i.1 : ℕ) : ℤ)) ((i.1 : ℕ) : ℤ) → a k = 0) ∧
      ∀ x, gateH L tbl G i γ x = trig L a x := by
  obtain ⟨dV, hdV, hd⟩ := gate_state_hasDerivAt L tbl G i γ hγ0 dγ hdγ
  obtain ⟨a, han, -, ha⟩ := dSerial_pairing_trig L _ dV
    (fun ℓ => blockProd_mem _ tbl _ fun g => hG _) i.1 hdV
  refine ⟨a, han, fun x => ?_⟩
  unfold gateH
  rw [show gateTangent L tbl G i γ x = _ from (hd x).deriv]
  exact ha x

/-- **Lemma 4.2, locality.** `h` depends only on the gates up to and including gate `i`: changing any later gate
    (within SU(2)) leaves it unchanged.
    (The hypotheses `hγ` and `hγ0` are kept as stated in the paper; the proof does not need them.) -/
theorem gate_tangent_local (L tbl : ℕ) (G G' : Gates L tbl (Fin 2)) (hG : InSU G) (hG' : InSU G')
    (i : Fin (L + 1) × Fin tbl)
    (hagree : ∀ i' : Fin (L + 1) × Fin tbl, (i'.1 < i.1 ∨ (i'.1 = i.1 ∧ i'.2 ≤ i.2)) → G' i' = G i')
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (_hγ : ∀ s, γ s ∈ Matrix.unitaryGroup (Fin 2) ℂ) (_hγ0 : γ 0 = G i)
    (dγ : Matrix (Fin 2) (Fin 2) ℂ) (hdγ : ∀ a b, HasDerivAt (fun s => γ s a b) (dγ a b) 0) (x : ℝ) :
    gateH L tbl G' i γ x = gateH L tbl G i γ x := by
  obtain ⟨φ, hφ⟩ := gate_split L tbl G i
  have key : ∀ G₁ : Gates L tbl (Fin 2), InSU G₁ → (∀ i', GateBefore i' i → G₁ i' = G i') → G₁ i = G i →
      gateH L tbl G₁ i γ x = ip (T (G i *ᵥ φ x)) (dγ *ᵥ φ x) := by
    intro G₁ hG₁ hb hi
    obtain ⟨Dn, hDn, hDS⟩ := hφ G₁ hb
    have hst : gateState L tbl G₁ x = Dn x *ᵥ (G i *ᵥ φ x) := by
      rw [← hi, ← hDn, perturb_self]
    have htg : gateTangent L tbl G₁ i γ x = Dn x *ᵥ (dγ *ᵥ φ x) := by
      unfold gateTangent
      simp_rw [hDn]
      exact (hasDerivAt_mulVec_mulVec_const (Dn x) γ dγ hdγ (φ x)).deriv
    unfold gateH
    rw [hst, htg, gauge_invariance _ (hDS hG₁ x)]
  rw [key G' hG' (fun i' h => hagree i' (h.imp id fun h => ⟨h.1, le_of_lt h.2⟩))
      (hagree i (Or.inr ⟨rfl, le_rfl⟩)),
    key G hG (fun _ _ => rfl) rfl]

/-- Pauli matrices `I, X, Y, Z`. -/
def pauli1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- Non-identity Pauli words on one qubit. -/
def pauli (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := pauli1 a.succ

/-- Coordinate curve of a Lie-algebra coordinate: `U exp(isP) = U (cos s · I + i sin s · P)` for a Pauli word `P`
    (`P² = I`). -/
def lieCurve {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  U * ((Real.cos s : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (Real.sin s : ℂ)) • P)

theorem lieCurve_unitary {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hP : Pᴴ = P) (hP2 : P * P = 1) (s : ℝ) :
    lieCurve U P s ∈ Matrix.unitaryGroup n ℂ := by
  have hA : ((Real.cos s : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (Real.sin s : ℂ)) • P) ∈
      Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hs : star ((Real.cos s : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (Real.sin s : ℂ)) • P) =
        (Real.cos s : ℂ) • (1 : Matrix n n ℂ) + (-(Complex.I * (Real.sin s : ℂ))) • P := by
      rw [star_add, star_smul, star_smul, star_one]
      change _ + _ • Pᴴ = _
      rw [hP, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      congr 2; ring
    rw [hs]
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hP2]
    have hc : (Real.cos s : ℂ) ^ 2 + (Real.sin s : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq s
    set c := (Real.cos s : ℂ)
    set d := (Real.sin s : ℂ)
    calc _ = (c * c + (Complex.I * d) * (-(Complex.I * d))) • (1 : Matrix n n ℂ) +
          (Complex.I * d * c + c * (-(Complex.I * d))) • P := by module
      _ = 1 := by
        rw [show c * c + (Complex.I * d) * (-(Complex.I * d)) = 1 by
              linear_combination hc - d ^ 2 * Complex.I_sq,
            show Complex.I * d * c + c * (-(Complex.I * d)) = 0 by ring]
        simp
  exact mul_mem hU hA

/-- Expanded form of the coordinate curve. -/
theorem lieCurve_eq {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ) (s : ℝ) :
    lieCurve U P s = (Real.cos s : ℂ) • U + (Complex.I * (Real.sin s : ℂ)) • (U * P) := by
  simp [lieCurve, mul_add]

theorem lieCurve_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ) (a b : n) :
    HasDerivAt (fun s => lieCurve U P s a b) ((U * (Complex.I • P)) a b) 0 := by
  simp only [lieCurve_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := (Real.hasDerivAt_cos 0).ofReal_comp
  have h2 := (Real.hasDerivAt_sin 0).ofReal_comp
  have := (h1.mul_const (U a b)).add ((h2.const_mul Complex.I).mul_const ((U * P) a b))
  convert this using 1
  simp

theorem lieCurve_zero {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ) : lieCurve U P 0 = U := by
  simp [lieCurve]

/-- Real coefficient vector `c̃ = (Re c₀, Re c₁, Im c₁, …)` of the serial output (Definition 3.2). -/
def gateCoeffVec (L tbl : ℕ) (G : Gates L tbl (Fin 2)) : Fin (2 * L + 1) → ℝ :=
  realRep L (realFourierCoeff (gateModel L tbl G))

/-- Lie-algebra coordinates of the serial circuit: gate, Pauli word. -/
abbrev SIdx (L tbl : ℕ) := Fin (L + 1) × Fin tbl × Fin 3

/-- **Definition 3.2.** Coefficient Jacobian `J = ∂c̃/∂θ` in Lie-algebra coordinates at the current gates. -/
def gateJ (L tbl : ℕ) (G : Gates L tbl (Fin 2)) : Matrix (Fin (2 * L + 1)) (SIdx L tbl) ℝ :=
  fun r j => deriv (fun s => gateCoeffVec L tbl
    (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)) r) 0

/-- The expectation value of a Hermitian observable in a serial state is a real trigonometric polynomial of
    degree ≤ L. -/
theorem serial_expval_trig (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : Mᴴ = M) :
    ∃ c : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0) ∧
      ∀ x, (((ip (serialState L V x) (M *ᵥ serialState L V x)).re : ℝ) : ℂ) = trig L c x := by
  obtain ⟨cs, hcs, hsrep⟩ := serialState_expansion L V
  obtain ⟨cs', hcs', hsT⟩ := expansion_eq_T L cs hcs
  obtain ⟨a, ha, haeq⟩ := pairing_integer_frequencies L cs' cs hcs' hcs M
  refine ⟨a, ha, fun x => ?_⟩
  have hψs : serialState L V x = fun i => ∑ k ∈ Finset.Icc (-(L : ℤ)) L,
      cs i k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) := funext (hsrep x)
  have hreal := ip_herm_im hM (serialState L V x)
  have h1 : (((ip (serialState L V x) (M *ᵥ serialState L V x)).re : ℝ) : ℂ) =
      ip (serialState L V x) (M *ᵥ serialState L V x) := by
    apply Complex.ext <;> simp [hreal]
  rw [h1, ← haeq x, ← hsT x, ← hψs]

/-- The serial output is a real trigonometric polynomial of degree ≤ L. -/
theorem gateModel_trig (L tbl : ℕ) (G : Gates L tbl (Fin 2)) :
    ∃ c : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0) ∧
      ∀ x, ((gateModel L tbl G x : ℝ) : ℂ) = trig L c x :=
  serial_expval_trig L _ Zm Zm_hermitian

/-- Serial instance of Theorem 3.1 in design form: `f(x) = Σ_r B_r(x) c̃_r`. -/
theorem gate_model_eq_design (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (x : ℝ) :
    gateModel L tbl G x = ∑ r, designEntry L x r * gateCoeffVec L tbl G r := by
  obtain ⟨c, hc, hcx⟩ := gateModel_trig L tbl G
  exact design_form_of_trig L c hc _ hcx x

theorem gateCoeffVec_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (j : SIdx L tbl) (r : Fin (2 * L + 1)) :
    HasDerivAt (fun s => gateCoeffVec L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)) r) (gateJ L tbl G r j) 0 := by
  set Gs : ℝ → Gates L tbl (Fin 2) :=
    fun s => perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s) with hGs
  set B := designMatrix L (eqGrid L 0) with hB
  have hrep : ∀ s, gateCoeffVec L tbl (Gs s) =
      B⁻¹ *ᵥ (fun k => gateModel L tbl (Gs s) (eqGrid L 0 k)) := by
    intro s
    conv_lhs => rw [vec_eq_design_inv L 0 (gateCoeffVec L tbl (Gs s))]
    congr 1
    funext k
    rw [gate_model_eq_design]
  have hdiff : ∀ k, DifferentiableAt ℝ (fun s => gateModel L tbl (Gs s) (eqGrid L 0 k)) 0 := by
    intro k
    obtain ⟨dV, -, hd⟩ := gate_state_hasDerivAt L tbl G (j.1, j.2.1)
      (lieCurve (G (j.1, j.2.1)) (pauli j.2.2)) (lieCurve_zero _ _) _
      (lieCurve_hasDerivAt (G (j.1, j.2.1)) (pauli j.2.2))
    exact (expval_hasDerivAt Zm Zm_hermitian _ _ 0 (hd (eqGrid L 0 k))).differentiableAt
  have hd : DifferentiableAt ℝ (fun s => gateCoeffVec L tbl (Gs s) r) 0 := by
    have : (fun s => gateCoeffVec L tbl (Gs s) r) =
        fun s => ∑ k, B⁻¹ r k * gateModel L tbl (Gs s) (eqGrid L 0 k) := by
      funext s
      rw [hrep s]
      rfl
    rw [this]
    exact DifferentiableAt.fun_sum fun k _ => (hdiff k).const_mul _
  exact hd.hasDerivAt

theorem pauli_herm (a : Fin 3) : (pauli a)ᴴ = pauli a := by
  ext i k
  fin_cases a <;> fin_cases i <;> fin_cases k <;> simp [pauli, pauli1, Matrix.conjTranspose_apply]

theorem pauli_sq (a : Fin 3) : pauli a * pauli a = 1 := by
  ext i k
  fin_cases a <;> fin_cases i <;> fin_cases k <;> simp [pauli, pauli1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The real coefficient vector of `2 Re[conj(h) μ]` is `A_μ` applied to the real coefficients of `h`. -/
theorem realRep_envCoeff (L : ℕ) (a b : ℤ → ℂ) (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0)
    (r : Fin (2 * L + 1)) :
    realRep L (envCoeff L a b) r = ∑ s, envMatrix L b r s * coeffVec L a s := by
  have h2 : envCoeff L a b =
      fun m => ∑ s, (coeffVec L a s : ℂ) * envCoeff L (coeffBasis L s) b m := by
    funext m
    rw [← envCoeff_real_sum]
    congr 1
    exact funext (coeffBasis_expansion L a ha)
  rw [h2, realRep_real_sum]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-- Fourier coefficients of `2 Re[conj(trig L a) trig L b]` in the band `[-L, L]`. -/
theorem realFourierCoeff_envelope (L : ℕ) (a b : ℤ → ℂ) (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0)
    (hb : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0) (m : ℤ) (hm : m ∈ Finset.Icc (-(L : ℤ)) L) :
    realFourierCoeff (fun x => 2 * ((starRingEnd ℂ) (trig L a x) * trig L b x).re) m = envCoeff L a b m := by
  unfold realFourierCoeff
  simp_rw [envelope_expansion L a b ha hb]
  rw [fourier_coeff_sum, if_pos]
  simp only [Finset.mem_Icc] at hm ⊢
  omega

/-- Column `j` of the coefficient Jacobian is the real coefficient vector of `2 Re[conj(h_j) μ]`. -/
theorem gateJ_column (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (j : SIdx L tbl) (a b : ℤ → ℂ)
    (ha : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) (hb : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0)
    (hμ : ∀ x, gateMu L tbl G x = trig L b x)
    (hh : ∀ x, gateH L tbl G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2)) x = trig L a x) :
    (fun r => gateJ L tbl G r j) = realRep L (envCoeff L a b) := by
  set i : Fin (L + 1) × Fin tbl := (j.1, j.2.1) with hi
  set γ := lieCurve (G i) (pauli j.2.2) with hγ
  have hPL : ∀ x, HasDerivAt (fun s => gateModel L tbl (perturb G i (γ s)) x)
      (2 * ((starRingEnd ℂ) (gateH L tbl G i γ x) * gateMu L tbl G x).re) 0 :=
    fun x => gate_phase_locking L tbl G hG i γ
      (lieCurve_unitary (G i) (pauli j.2.2) (hG i).1 (pauli_herm _) (pauli_sq _)) (lieCurve_zero _ _) _
      (lieCurve_hasDerivAt (G i) (pauli j.2.2)) x
  have hDS : ∀ x, HasDerivAt (fun s => gateModel L tbl (perturb G i (γ s)) x)
      (∑ r, designEntry L x r * gateJ L tbl G r j) 0 := by
    intro x
    have : (fun s => gateModel L tbl (perturb G i (γ s)) x) =
        fun s => ∑ r, designEntry L x r * gateCoeffVec L tbl (perturb G i (γ s)) r := by
      funext s; exact gate_model_eq_design L tbl _ x
    rw [this]
    exact HasDerivAt.fun_sum fun r _ => (gateCoeffVec_hasDerivAt L tbl G j r).const_mul _
  have heq : (fun x => ∑ r, designEntry L x r * gateJ L tbl G r j) =
      fun x => 2 * ((starRingEnd ℂ) (trig L a x) * trig L b x).re := by
    funext x
    rw [(hDS x).unique (hPL x), hh x, hμ x]
  rw [← realRep_realFourierCoeff_design L (fun r => gateJ L tbl G r j), heq]
  exact realRep_congr L _ _ (realFourierCoeff_envelope L a b ha hb)

/-- **Eq. (2).** `J = A_μ H`: `A_μ = envMatrix L b` is built from the envelope coefficients `b` alone, and column
    `j` of `H` is the real coefficient vector of `h_j`. -/
theorem gate_coeffJac_factorisation (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    ∃ b : ℤ → ℂ, (∀ x, gateMu L tbl G x = trig L b x) ∧
      ∃ H : Matrix (Fin (2 * (2 * L + 1))) (SIdx L tbl) ℝ, gateJ L tbl G = envMatrix L b * H ∧
        ∀ j : SIdx L tbl, ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
          (∀ x, gateH L tbl G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2)) x = trig L a x) ∧
          (fun s => H s j) = coeffVec L a := by
  obtain ⟨b, hb, hbeq⟩ := gate_envelope_trig L tbl G
  have hA : ∀ j : SIdx L tbl, ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
      ∀ x, gateH L tbl G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2)) x = trig L a x := by
    intro j
    obtain ⟨a, ha, haeq⟩ := gate_tangent_trig L tbl G hG (j.1, j.2.1)
      (lieCurve (G (j.1, j.2.1)) (pauli j.2.2))
      (lieCurve_unitary _ _ (hG _).1 (pauli_herm _) (pauli_sq _)) (lieCurve_zero _ _) _
      (lieCurve_hasDerivAt _ _)
    refine ⟨a, fun k hk => ha k fun h => hk ?_, haeq⟩
    have := j.1.isLt
    simp only [Finset.mem_Icc] at h ⊢
    omega
  choose a ha haeq using hA
  refine ⟨b, hbeq, fun s j => coeffVec L (a j) s, ?_, fun j => ⟨a j, ha j, haeq j, rfl⟩⟩
  ext r j
  rw [Matrix.mul_apply, ← realRep_envCoeff L (a j) b (ha j)]
  exact congrFun (gateJ_column L tbl G hG j (a j) b (ha j) hb hbeq (haeq j)) r

end

end


/-! # Section 16: Lemma 3.2 and Lemma B.3 -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 16. Lemma 3.2 and Lemma B.3, for any circuit whose output has degree ≤ L -/

/-- **Lemma 3.2, `J_data = BJ`.** If the output along each coordinate curve is a real trigonometric polynomial of
    degree ≤ L with coefficient vector `C j s` (Theorem 3.1) and `J` is the coefficient Jacobian, the data Jacobian at
    inputs `x` is `BJ`. -/
theorem dataJac_eq_design_mul {ι : Type*} [Fintype ι] (L : ℕ) (F : ι → ℝ → ℝ → ℝ)
    (C : ι → ℝ → Fin (2 * L + 1) → ℝ) (hF : ∀ j s x, F j s x = ∑ r, designEntry L x r * C j s r)
    (J : Matrix (Fin (2 * L + 1)) ι ℝ) (hJ : ∀ j r, HasDerivAt (fun s => C j s r) (J r j) 0)
    {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (j : ι) :
    HasDerivAt (fun s => F j s (x i)) ((designMatrix L x * J) i j) 0 := by
  have h : HasDerivAt (fun s => ∑ r, designEntry L (x i) r * C j s r)
      (∑ r, designEntry L (x i) r * J r j) 0 :=
    HasDerivAt.fun_sum (fun r _ => (hJ j r).const_mul _)
  simp_rw [hF]
  convert h using 1

/-- Euclidean norm. -/
def eNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- Largest and smallest singular value `σ₁`, `σ_m` of a matrix with `m` rows, as the extremes of `‖Mᵀy‖` over unit
    vectors `y`. -/
def sigmaMax {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin m) ι ℝ) : ℝ :=
  sSup {t | ∃ y : Fin m → ℝ, eNorm y = 1 ∧ t = eNorm (Mᵀ *ᵥ y)}

def sigmaMin {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin m) ι ℝ) : ℝ :=
  sInf {t | ∃ y : Fin m → ℝ, eNorm y = 1 ∧ t = eNorm (Mᵀ *ᵥ y)}

theorem eNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

theorem eNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) : eNorm (c • v) = |c| * eNorm v := by
  unfold eNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

theorem eNorm_eq_zero {ι : Type*} [Fintype ι] (v : ι → ℝ) (h : eNorm v = 0) : v = 0 := by
  unfold eNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 h i (Finset.mem_univ _)
  simpa using this

theorem eNorm_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) : eNorm v ≤ ∑ i, |v i| := by
  unfold eNorm
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  calc ∑ i, v i ^ 2 = ∑ i, |v i| ^ 2 := by simp
    _ ≤ (∑ i, |v i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

/-- The set whose extremes define `sigmaMin` and `sigmaMax`. -/
theorem singSet_nonempty {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin (m + 1)) ι ℝ) :
    {t | ∃ y : Fin (m + 1) → ℝ, eNorm y = 1 ∧ t = eNorm (Mᵀ *ᵥ y)}.Nonempty :=
  ⟨_, Pi.single 0 1, by simp [eNorm, Pi.single_apply], rfl⟩

theorem singSet_bddBelow {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin m) ι ℝ) :
    BddBelow {t | ∃ y : Fin m → ℝ, eNorm y = 1 ∧ t = eNorm (Mᵀ *ᵥ y)} :=
  ⟨0, fun _ ⟨_, _, ht⟩ => ht ▸ eNorm_nonneg _⟩

theorem singSet_bddAbove {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin m) ι ℝ) :
    BddAbove {t | ∃ y : Fin m → ℝ, eNorm y = 1 ∧ t = eNorm (Mᵀ *ᵥ y)} := by
  refine ⟨∑ j, ∑ i, |M i j|, fun t ⟨y, hy, ht⟩ => ?_⟩
  rw [ht]
  refine (eNorm_le_sum_abs _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hyi : ∀ i, |y i| ≤ 1 := by
    intro i
    have h1 : y i ^ 2 ≤ ∑ k, y k ^ 2 :=
      Finset.single_le_sum (f := fun k => y k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ k, y k ^ 2 = 1 := by
      unfold eNorm at hy
      have := Real.sq_sqrt (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (y k))
      rw [hy] at this; linarith
    rw [h2] at h1
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hyi i)

theorem sigmaMin_nonneg {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin (m + 1)) ι ℝ) : 0 ≤ sigmaMin M :=
  le_csInf (singSet_nonempty M) fun _ ⟨_, _, ht⟩ => ht ▸ eNorm_nonneg _

theorem sigmaMax_nonneg {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin (m + 1)) ι ℝ) : 0 ≤ sigmaMax M := by
  obtain ⟨t, ht⟩ := singSet_nonempty M
  obtain ⟨y, _, rfl⟩ := ht
  exact (eNorm_nonneg _).trans (le_csSup (singSet_bddAbove M) ⟨y, by assumption, rfl⟩)

/-- On the grid, `√n ‖y‖ ≤ ‖Bᵀ y‖ ≤ √(2n) ‖y‖`. -/
theorem grid_Bt_bounds (L : ℕ) (x₀ : ℝ) (y : Fin (2 * L + 1) → ℝ) :
    Real.sqrt (2 * L + 1) * eNorm y ≤ eNorm ((designMatrix L (eqGrid L x₀))ᵀ *ᵥ y) ∧
    eNorm ((designMatrix L (eqGrid L x₀))ᵀ *ᵥ y) ≤ Real.sqrt (2 * (2 * L + 1)) * eNorm y := by
  set B := designMatrix L (eqGrid L x₀) with hB
  set N : ℝ := 2 * L + 1 with hN
  have hNpos : 0 < N := by positivity
  set Dg : Fin (2 * L + 1) → ℝ := fun r => if (r : ℕ) = 0 then N else 2 * N with hDg
  have hgram : Bᵀ * B = Matrix.diagonal Dg := design_gram_eqGrid L x₀
  have hDpos : ∀ r, 0 < Dg r := fun r => by simp only [hDg]; split_ifs <;> positivity
  have hDlo : ∀ r, N ≤ Dg r := fun r => by simp only [hDg]; split_ifs <;> linarith
  have hDhi : ∀ r, Dg r ≤ 2 * N := fun r => by simp only [hDg]; split_ifs <;> linarith
  set w := Bᵀ *ᵥ y with hw
  set u : Fin (2 * L + 1) → ℝ := fun r => w r / Dg r with hu
  have hBinj : ∀ a b : Fin (2 * L + 1) → ℝ, Bᵀ *ᵥ a = Bᵀ *ᵥ b → a = b := by
    intro a b hab
    have hdet : IsUnit (Bᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (design_det_ne_zero L x₀)
    have := congrArg (fun v => (Bᵀ)⁻¹ *ᵥ v) hab
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet] using this
  have hyu : y = B *ᵥ u := by
    apply hBinj
    rw [Matrix.mulVec_mulVec, hgram, ← hw]
    funext r
    simp only [Matrix.mulVec_diagonal, hu]
    rw [mul_div_cancel₀ _ (hDpos r).ne']
  have hQ : ∑ i, y i ^ 2 = ∑ r, w r ^ 2 / Dg r := by
    have h1 : ∑ i, y i ^ 2 = (B *ᵥ u) ⬝ᵥ (B *ᵥ u) := by
      rw [← hyu]; simp [dotProduct, sq]
    rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hyu, ← hw, dotProduct_comm]
    simp only [dotProduct, hu]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  have hlo : ∑ r, w r ^ 2 / (2 * N) ≤ ∑ i, y i ^ 2 := by
    rw [hQ]
    exact Finset.sum_le_sum fun r _ => div_le_div_of_nonneg_left (sq_nonneg _) (hDpos r) (hDhi r)
  have hhi : ∑ i, y i ^ 2 ≤ ∑ r, w r ^ 2 / N := by
    rw [hQ]
    exact Finset.sum_le_sum fun r _ => div_le_div_of_nonneg_left (sq_nonneg _) hNpos (hDlo r)
  rw [← Finset.sum_div] at hlo hhi
  unfold eNorm
  rw [← Real.sqrt_mul hNpos.le, ← Real.sqrt_mul (by positivity)]
  constructor
  · apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hNpos] at hhi
    linarith
  · apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)] at hlo
    linarith

theorem grid_Bt_surj (L : ℕ) (x₀ : ℝ) (z : Fin (2 * L + 1) → ℝ) :
    ∃ y, (designMatrix L (eqGrid L x₀))ᵀ *ᵥ y = z := by
  have hdet : IsUnit ((designMatrix L (eqGrid L x₀))ᵀ).det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (design_det_ne_zero L x₀)
  exact ⟨((designMatrix L (eqGrid L x₀))ᵀ)⁻¹ *ᵥ z, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩

/-- **Lemma 3.2, the grid.** On `2L+1` equispaced points, `σ₁` and `σ_{2L+1}` of `J_data = BJ` are those of `J` up to
    factors in `[√n, √(2n)]`, `n = 2L+1`; hence `κ_J` on the grid is within a factor `√2` of `κ_J` of `J`
    (`κ(B) = √2` by `design_gram_eqGrid`). -/
theorem grid_singular_bounds {ι : Type*} [Fintype ι] (L : ℕ) (x₀ : ℝ) (J : Matrix (Fin (2 * L + 1)) ι ℝ) :
    Real.sqrt (2 * L + 1) * sigmaMin J ≤ sigmaMin (designMatrix L (eqGrid L x₀) * J) ∧
    sigmaMin (designMatrix L (eqGrid L x₀) * J) ≤ Real.sqrt (2 * (2 * L + 1)) * sigmaMin J ∧
    Real.sqrt (2 * L + 1) * sigmaMax J ≤ sigmaMax (designMatrix L (eqGrid L x₀) * J) ∧
    sigmaMax (designMatrix L (eqGrid L x₀) * J) ≤ Real.sqrt (2 * (2 * L + 1)) * sigmaMax J := by
  set B := designMatrix L (eqGrid L x₀) with hB
  set a := Real.sqrt (2 * L + 1) with ha
  set b := Real.sqrt (2 * (2 * L + 1)) with hb
  have hapos : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hbpos : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hT : ∀ y, (B * J)ᵀ *ᵥ y = Jᵀ *ᵥ (Bᵀ *ᵥ y) := fun y => by
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
  have hdec : ∀ w : Fin (2 * L + 1) → ℝ, eNorm w ≠ 0 →
      eNorm ((eNorm w)⁻¹ • w) = 1 ∧ eNorm (Jᵀ *ᵥ w) = eNorm w * eNorm (Jᵀ *ᵥ ((eNorm w)⁻¹ • w)) := by
    intro w hw
    have hpos : 0 < eNorm w := lt_of_le_of_ne (eNorm_nonneg _) (Ne.symm hw)
    refine ⟨?_, ?_⟩
    · rw [eNorm_smul, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hw]
    · rw [Matrix.mulVec_smul, eNorm_smul, abs_of_pos (inv_pos.2 hpos), ← mul_assoc, mul_inv_cancel₀ hw,
        one_mul]
  have hSJne := singSet_nonempty J
  have hSBne := singSet_nonempty (B * J)
  have hJmin := sigmaMin_nonneg J
  have hJmax := sigmaMax_nonneg J
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_csInf hSBne
    rintro t ⟨y, hy, rfl⟩
    rw [hT]
    obtain ⟨hlo, -⟩ := grid_Bt_bounds L x₀ y
    rw [hy, mul_one] at hlo
    have hw0 : eNorm (Bᵀ *ᵥ y) ≠ 0 := (lt_of_lt_of_le hapos hlo).ne'
    obtain ⟨hz, hJz⟩ := hdec _ hw0
    rw [hJz]
    have : sigmaMin J ≤ eNorm (Jᵀ *ᵥ ((eNorm (Bᵀ *ᵥ y))⁻¹ • (Bᵀ *ᵥ y))) :=
      csInf_le (singSet_bddBelow J) ⟨_, hz, rfl⟩
    exact mul_le_mul hlo this hJmin (eNorm_nonneg _)
  · have key : sigmaMin (B * J) / b ≤ sigmaMin J := by
      apply le_csInf hSJne
      rintro t ⟨z, hz, rfl⟩
      obtain ⟨y0, hy0⟩ := grid_Bt_surj L x₀ z
      obtain ⟨-, hhi⟩ := grid_Bt_bounds L x₀ y0
      rw [hy0, hz] at hhi
      have hy0pos : 0 < eNorm y0 := by
        by_contra h
        have : eNorm y0 = 0 := le_antisymm (not_lt.1 h) (eNorm_nonneg _)
        rw [this, mul_zero] at hhi; linarith
      obtain ⟨hyn, -⟩ := hdec y0 hy0pos.ne'
      have hle : sigmaMin (B * J) ≤ eNorm ((B * J)ᵀ *ᵥ ((eNorm y0)⁻¹ • y0)) :=
        csInf_le (singSet_bddBelow _) ⟨_, hyn, rfl⟩
      rw [hT, Matrix.mulVec_smul, hy0, Matrix.mulVec_smul, eNorm_smul, abs_of_pos (inv_pos.2 hy0pos)] at hle
      rw [div_le_iff₀ hbpos]
      have hinv : (eNorm y0)⁻¹ ≤ b := by
        rw [inv_le_iff_one_le_mul₀ hy0pos]; linarith
      calc sigmaMin (B * J) ≤ (eNorm y0)⁻¹ * eNorm (Jᵀ *ᵥ z) := hle
        _ ≤ b * eNorm (Jᵀ *ᵥ z) := mul_le_mul_of_nonneg_right hinv (eNorm_nonneg _)
        _ = eNorm (Jᵀ *ᵥ z) * b := mul_comm _ _
    rw [div_le_iff₀ hbpos] at key
    linarith
  · have key : sigmaMax J ≤ sigmaMax (B * J) / a := by
      apply csSup_le hSJne
      rintro t ⟨z, hz, rfl⟩
      obtain ⟨y0, hy0⟩ := grid_Bt_surj L x₀ z
      obtain ⟨hlo, hhi⟩ := grid_Bt_bounds L x₀ y0
      rw [hy0, hz] at hhi hlo
      have hy0pos : 0 < eNorm y0 := by
        by_contra h
        have : eNorm y0 = 0 := le_antisymm (not_lt.1 h) (eNorm_nonneg _)
        rw [this, mul_zero] at hhi; linarith
      obtain ⟨hyn, -⟩ := hdec y0 hy0pos.ne'
      have hle : eNorm ((B * J)ᵀ *ᵥ ((eNorm y0)⁻¹ • y0)) ≤ sigmaMax (B * J) :=
        le_csSup (singSet_bddAbove _) ⟨_, hyn, rfl⟩
      rw [hT, Matrix.mulVec_smul, hy0, Matrix.mulVec_smul, eNorm_smul, abs_of_pos (inv_pos.2 hy0pos)] at hle
      rw [le_div_iff₀ hapos]
      have hinv : a ≤ (eNorm y0)⁻¹ := by
        rw [le_inv_comm₀ hapos hy0pos]
        rw [inv_eq_one_div, le_div_iff₀ hapos]; linarith
      calc eNorm (Jᵀ *ᵥ z) * a = a * eNorm (Jᵀ *ᵥ z) := mul_comm _ _
        _ ≤ (eNorm y0)⁻¹ * eNorm (Jᵀ *ᵥ z) := mul_le_mul_of_nonneg_right hinv (eNorm_nonneg _)
        _ ≤ sigmaMax (B * J) := hle
    rw [le_div_iff₀ hapos] at key
    linarith
  · apply csSup_le hSBne
    rintro t ⟨y, hy, rfl⟩
    rw [hT]
    obtain ⟨-, hhi⟩ := grid_Bt_bounds L x₀ y
    rw [hy, mul_one] at hhi
    by_cases hw0 : eNorm (Bᵀ *ᵥ y) = 0
    · rw [eNorm_eq_zero _ hw0, Matrix.mulVec_zero]
      have : eNorm (0 : ι → ℝ) = 0 := by simp [eNorm]
      rw [this]
      positivity
    obtain ⟨hz, hJz⟩ := hdec _ hw0
    rw [hJz]
    have : eNorm (Jᵀ *ᵥ ((eNorm (Bᵀ *ᵥ y))⁻¹ • (Bᵀ *ᵥ y))) ≤ sigmaMax J :=
      le_csSup (singSet_bddAbove J) ⟨_, hz, rfl⟩
    exact mul_le_mul hhi this (eNorm_nonneg _) hbpos.le

/-- Linear-algebra core of Lemma B.3, for columns indexed by any finite type. -/
theorem lsq_of_normal_gen {n m : ℕ} {κ : Type*} [Fintype κ] (B : Matrix (Fin n) (Fin m) ℝ)
    (J : Matrix (Fin m) κ ℝ) (c : Fin m → ℝ) (y : Fin n → ℝ) (hJ : J.rank = m)
    (hgrad : (B * J)ᵀ *ᵥ (B *ᵥ c - y) = 0) (c' : Fin m → ℝ) :
    ∑ i, ((B *ᵥ c) i - y i) ^ 2 ≤ ∑ i, ((B *ᵥ c') i - y i) ^ 2 := by
  set r := B *ᵥ c - y with hr
  have hinj : ∀ w : Fin m → ℝ, Jᵀ *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hrk : Jᵀ.rank = m := by rw [Matrix.rank_transpose, hJ]
    have hker := LinearMap.finrank_range_add_finrank_ker (Jᵀ.mulVecLin)
    rw [← Matrix.rank, hrk, Module.finrank_fin_fun] at hker
    have h0 : Module.finrank ℝ (LinearMap.ker Jᵀ.mulVecLin) = 0 := by omega
    have hbot := Submodule.finrank_eq_zero.mp h0
    have : w ∈ LinearMap.ker Jᵀ.mulVecLin := LinearMap.mem_ker.mpr hw
    rw [hbot] at this
    simpa using this
  have hBr : Bᵀ *ᵥ r = 0 := by
    apply hinj
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    exact hgrad
  set d := c' - c with hd
  have hdot : ∑ i, (B *ᵥ d) i * r i = 0 := by
    have : (B *ᵥ d) ⬝ᵥ r = d ⬝ᵥ (Bᵀ *ᵥ r) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hBr, dotProduct_zero] at this
    simpa [dotProduct] using this
  have hc' : ∀ i, (B *ᵥ c') i - y i = (B *ᵥ d) i + r i := by
    intro i
    simp only [hd, hr, Matrix.mulVec_sub, Pi.sub_apply]
    ring
  simp_rw [hc']
  have : ∑ i, ((B *ᵥ d) i + r i) ^ 2 = ∑ i, ((B *ᵥ d) i) ^ 2 + 2 * ∑ i, (B *ᵥ d) i * r i + ∑ i, r i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hdot]
  have : 0 ≤ ∑ i, ((B *ᵥ d) i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [hr, Pi.sub_apply] at this ⊢
  linarith

/-- **Lemma B.3.** At a stationary point of the training loss where `J` has full row rank, the model is a least-squares
    fit of the data among all real trigonometric polynomials of degree ≤ L (whose values at `x` are the vectors
    `B c'`, `real_trig_eq_design`). -/
theorem stationary_is_least_squares {ι : Type*} [Fintype ι] (L : ℕ) (F : ι → ℝ → ℝ → ℝ)
    (C : ι → ℝ → Fin (2 * L + 1) → ℝ) (hF : ∀ j s x, F j s x = ∑ r, designEntry L x r * C j s r)
    (J : Matrix (Fin (2 * L + 1)) ι ℝ) (hJ : ∀ j r, HasDerivAt (fun s => C j s r) (J r j) 0)
    (c : Fin (2 * L + 1) → ℝ) (hc : ∀ j, C j 0 = c) {n : ℕ} (x y : Fin n → ℝ)
    (hrank : J.rank = 2 * L + 1)
    (hstat : ∀ j, HasDerivAt (fun s => (1 / n : ℝ) * ∑ i, (F j s (x i) - y i) ^ 2) 0 0)
    (c' : Fin (2 * L + 1) → ℝ) :
    (1 / n : ℝ) * ∑ i, ((designMatrix L x *ᵥ c) i - y i) ^ 2 ≤
      (1 / n : ℝ) * ∑ i, ((designMatrix L x *ᵥ c') i - y i) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  set B := designMatrix L x with hB
  have hFc : ∀ j i, F j 0 (x i) = (B *ᵥ c) i := by
    intro j i
    rw [hF, hc]
    simp [hB, mulVec, dotProduct, designEntry, designMatrix]
  have hgrad : (B * J)ᵀ *ᵥ (B *ᵥ c - y) = 0 := by
    funext j
    have hd : HasDerivAt (fun s => (1 / n : ℝ) * ∑ i, (F j s (x i) - y i) ^ 2)
        ((1 / n : ℝ) * ∑ i, 2 * (F j 0 (x i) - y i) * (B * J) i j) 0 := by
      apply HasDerivAt.const_mul
      apply HasDerivAt.fun_sum
      intro i _
      have h1 := ((dataJac_eq_design_mul L F C hF J hJ x i j).sub_const (y i)).pow 2
      rw [← hB] at h1
      convert h1 using 1
      push_cast
      ring
    have h0 := hd.unique (hstat j)
    have hn' : (1 / n : ℝ) ≠ 0 := by positivity
    have h2 : ∑ i, 2 * (F j 0 (x i) - y i) * (B * J) i j = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hn'
      · exact h
    simp only [hFc] at h2
    change ∑ i, (B * J)ᵀ j i * (B *ᵥ c - y) i = 0
    simp only [Matrix.transpose_apply, Pi.sub_apply]
    have : ∑ i, (B * J) i j * ((B *ᵥ c) i - y i) = (1 / 2) * ∑ i, 2 * ((B *ᵥ c) i - y i) * (B * J) i j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h2, mul_zero]
  have := lsq_of_normal_gen B J c y hrank hgrad c'
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- Lemma B.3 for the serial circuit.
    (The hypothesis `hG` is kept as stated in the paper; the proof does not need them.) -/
theorem serial_stationary_is_least_squares (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (_hG : InSU G) {n : ℕ}
    (x y : Fin n → ℝ) (hrank : (gateJ L tbl G).rank = 2 * L + 1)
    (hstat : ∀ j : SIdx L tbl, HasDerivAt (fun s => (1 / n : ℝ) * ∑ i,
      (gateModel L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)) (x i) - y i) ^ 2) 0 0)
    (c' : Fin (2 * L + 1) → ℝ) :
    (1 / n : ℝ) * ∑ i, (gateModel L tbl G (x i) - y i) ^ 2 ≤
      (1 / n : ℝ) * ∑ i, ((designMatrix L x *ᵥ c') i - y i) ^ 2 := by
  have h := stationary_is_least_squares L
    (fun (j : SIdx L tbl) s x =>
      gateModel L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)) x)
    (fun j s => gateCoeffVec L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)))
    (fun j s x => gate_model_eq_design L tbl _ x) (gateJ L tbl G)
    (fun j r => gateCoeffVec_hasDerivAt L tbl G j r) (gateCoeffVec L tbl G)
    (fun j => by simp only [lieCurve_zero, perturb_self]) x y hrank hstat c'
  have hl : ∀ i, gateModel L tbl G (x i) = (designMatrix L x *ᵥ gateCoeffVec L tbl G) i := by
    intro i
    rw [gate_model_eq_design]
    simp [mulVec, dotProduct, designEntry, designMatrix]
  simp_rw [hl]
  exact h

end

end


/-! # Section 17: the ancilla circuit -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 17. The ancilla circuit -/

/-- The SWAP gate on `(q₀, q₁)`. -/
def swapGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q => if p = (q.2, q.1) then 1 else 0

theorem swapGate_eq : swapGate = Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [swapGate, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.prodComm_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

theorem swapGate_det : swapGate.det = -1 := by
  rw [swapGate_eq, Matrix.det_permutation]
  have : Equiv.Perm.sign (Equiv.prodComm (Fin 2) (Fin 2) : Equiv.Perm (Fin 2 × Fin 2)) = -1 := by decide
  rw [this]; simp

theorem swapGate_mul_self : swapGate * swapGate = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, swapGate, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

theorem swapGate_star : star swapGate = swapGate := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.star_apply, swapGate]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

/-- `e^{iπ/4} · SWAP ∈ SU(4)`. -/
theorem phaseSwap_mem_SU4 :
    Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • swapGate ∈
      Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ := by
  set c := Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) with hc
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [hc, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show -Complex.I * ((Real.pi / 4 : ℝ) : ℂ) + Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = 0 by ring,
      Complex.exp_zero]
  have hc4 : c ^ 4 = -1 := by
    rw [hc, ← Complex.exp_nat_mul]
    push_cast
    rw [show (4 : ℂ) * (Complex.I * (Real.pi / 4)) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, ?_⟩
  · rw [star_smul, swapGate_star, smul_mul_smul_comm, swapGate_mul_self]
    simp [hcc]
  · rw [Matrix.det_smul, swapGate_det]
    simp [hc4]

/-- `V ⊗ I ∈ SU(4)` for `V ∈ SU(2)`. -/
theorem kron_one_mem_SU4 (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix.kronecker V (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hV ⊢
  obtain ⟨hU, hdet⟩ := hV
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
    rw [show star (Matrix.kronecker V (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        Matrix.kronecker (star V) (star (1 : Matrix (Fin 2) (Fin 2) ℂ)) from
      Matrix.conjTranspose_kronecker V 1]
    unfold Matrix.kronecker
    rw [star_one, ← Matrix.mul_kronecker_mul, hU, mul_one, Matrix.one_kronecker_one]
  · unfold Matrix.kronecker
    rw [Matrix.det_kronecker, hdet]
    simp

/-- `|00⟩`. -/
def ket00 : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 0) then 1 else 0

/-- Ancilla state `W_L (R_X(x) ⊗ I) W_{L−1} ⋯ (R_X(x) ⊗ I) W_0 |00⟩`: encoding on qubit 0. -/
def ancillaState : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) → ℝ → Fin 2 × Fin 2 → ℂ
  | 0, W, _ => W 0 *ᵥ ket00
  | L + 1, W, x => W (Fin.last (L + 1)) *ᵥ
      (Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ancillaState L (fun i => W (Fin.castSucc i)) x)

/-- Ancilla output: `Z` on qubit 1. -/
def ancillaModel (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) : ℝ :=
  (dotProduct (star (ancillaState L W x))
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x)).re

/-- Blocks realising the serial circuit: `V_ℓ ⊗ I` for `ℓ < L`, `e^{iπ/4} SWAP (V_L ⊗ I)` for `ℓ = L`. -/
def ancillaEmbed (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun ℓ =>
  if ℓ = Fin.last L then
    (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • swapGate) * Matrix.kronecker (V ℓ) 1
  else Matrix.kronecker (V ℓ) 1

theorem ancillaEmbed_mem_SU4 (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ ℓ, V ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (ℓ : Fin (L + 1)) :
    ancillaEmbed L V ℓ ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ := by
  unfold ancillaEmbed
  split_ifs
  · exact mul_mem phaseSwap_mem_SU4 (kron_one_mem_SU4 _ (hV ℓ))
  · exact kron_one_mem_SU4 _ (hV ℓ)

/-! ### Half-integer expansions of amplitudes -/

/-- `f(x) = Σ_{|k| ≤ ℓ, k ≡ ℓ (mod 2)} c_k e^{ikx/2}`. -/
def HalfExp (ℓ : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ c : ℤ → ℂ, (∀ k, c k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ)) ∧
    ∀ x, f x = ∑ k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ, c k * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2)

theorem HalfExp.const (a : ℂ) : HalfExp 0 (fun _ => a) := by
  refine ⟨fun k => if k = 0 then a else 0, fun k h => ?_, fun x => ?_⟩
  · by_cases hk : k = 0
    · subst hk; simp
    · simp [hk] at h
  · simp

theorem HalfExp.zero (ℓ : ℕ) : HalfExp ℓ (fun _ => 0) :=
  ⟨fun _ => 0, fun _ h => absurd rfl h, fun x => by simp⟩

theorem HalfExp.add {ℓ : ℕ} {f g : ℝ → ℂ} (hf : HalfExp ℓ f) (hg : HalfExp ℓ g) :
    HalfExp ℓ (fun x => f x + g x) := by
  obtain ⟨c, hc, hcx⟩ := hf
  obtain ⟨d, hd, hdx⟩ := hg
  refine ⟨fun k => c k + d k, fun k h => ?_, fun x => ?_⟩
  · simp only at h
    by_cases h1 : c k = 0
    · rw [h1, zero_add] at h; exact hd k h
    · exact hc k h1
  · beta_reduce
    rw [hcx, hdx, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem HalfExp.const_mul {ℓ : ℕ} {f : ℝ → ℂ} (a : ℂ) (hf : HalfExp ℓ f) :
    HalfExp ℓ (fun x => a * f x) := by
  obtain ⟨c, hc, hcx⟩ := hf
  refine ⟨fun k => a * c k, fun k h => hc k (right_ne_zero_of_mul h), fun x => ?_⟩
  beta_reduce
  rw [hcx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem HalfExp.sum {ℓ : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, HalfExp ℓ (f i)) :
    HalfExp ℓ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HalfExp.zero ℓ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem HalfExp.congr {ℓ : ℕ} {f g : ℝ → ℂ} (hf : HalfExp ℓ f) (h : ∀ x, f x = g x) : HalfExp ℓ g := by
  obtain ⟨c, hc, hcx⟩ := hf
  exact ⟨c, hc, fun x => (h x) ▸ hcx x⟩

/-- Multiplication by `e^{±ix/2}` raises the degree by one. -/
theorem HalfExp.mul_exp {ℓ : ℕ} {f : ℝ → ℂ} (s : ℤ) (hs : s = 1 ∨ s = -1) (hf : HalfExp ℓ f) :
    HalfExp (ℓ + 1) (fun x => Complex.exp (Complex.I * (s : ℂ) * (x : ℂ) / 2) * f x) := by
  obtain ⟨c, hc, hcx⟩ := hf
  have hc0 : ∀ j, j ∉ Finset.Icc (-(ℓ : ℤ)) ℓ → c j = 0 := fun j hj => by
    by_contra h; exact hj (hc j h).1
  refine ⟨fun k => c (k - s), fun k h => ?_, fun x => ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ h
    simp only [Finset.mem_Icc, Int.even_iff] at h1 h2 ⊢
    push_cast
    omega
  · beta_reduce
    rw [sum_Icc_shift ℓ s (by omega) c _ hc0, hcx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Multiplication by an entry of `R_X(x)` raises the degree by one. -/
theorem HalfExp.RX {ℓ : ℕ} {f : ℝ → ℂ} (a a' : Fin 2) (hf : HalfExp ℓ f) :
    HalfExp (ℓ + 1) (fun x => RXm x a a' * f x) := by
  set E : ℝ → ℤ → ℂ := fun x k => Complex.exp (Complex.I * (k : ℂ) * (x : ℂ) / 2) with hE
  have hcos : ∀ x : ℝ, Complex.cos ((x : ℂ) / 2) = (E x 1 + E x (-1)) / 2 := by
    intro x
    simp only [hE, Complex.cos]
    congr 2 <;> congr 1 <;> push_cast <;> ring
  have hsin : ∀ x : ℝ, -Complex.I * Complex.sin ((x : ℂ) / 2) = (E x (-1) - E x 1) / 2 := by
    intro x
    simp only [hE, Complex.sin]
    rw [show (Complex.I * ((-1 : ℤ) : ℂ) * (x : ℂ) / 2) = -((x : ℂ) / 2) * Complex.I by push_cast; ring,
      show (Complex.I * ((1 : ℤ) : ℂ) * (x : ℂ) / 2) = ((x : ℂ) / 2) * Complex.I by push_cast; ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  have h1 := HalfExp.mul_exp 1 (Or.inl rfl) hf
  have h2 := HalfExp.mul_exp (-1) (Or.inr rfl) hf
  by_cases haa : a = a'
  · subst haa
    refine ((h1.const_mul (1 / 2)).add (h2.const_mul (1 / 2))).congr fun x => ?_
    have hRX : RXm x a a = Complex.cos ((x : ℂ) / 2) := by
      fin_cases a <;> simp [RXm]
    rw [hRX, hcos]
    simp only [hE]
    ring
  · refine ((h2.const_mul (1 / 2)).add (h1.const_mul (-1 / 2))).congr fun x => ?_
    have hRX : RXm x a a' = -Complex.I * Complex.sin ((x : ℂ) / 2) := by
      fin_cases a <;> fin_cases a' <;> simp_all [RXm]
    rw [hRX, hsin]
    simp only [hE]
    ring

/-- The product `conj(f) g` of two half-integer expansions of the same degree and parity is an integer-frequency
    trigonometric polynomial. -/
theorem HalfExp.pair {ℓ : ℕ} {f g : ℝ → ℂ} (hf : HalfExp ℓ f) (hg : HalfExp ℓ g) :
    ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(ℓ : ℤ)) ℓ → a k = 0) ∧
      ∀ x, (starRingEnd ℂ) (f x) * g x = trig ℓ a x := by
  obtain ⟨c, hc, hcx⟩ := hf
  obtain ⟨d, hd, hdx⟩ := hg
  set cv : Fin 2 → ℤ → ℂ := ![c, fun _ => 0] with hcv
  set dv : Fin 2 → ℤ → ℂ := ![d, fun _ => 0] with hdv
  have hcvs : ∀ i k, cv i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ) := by
    intro i k h; fin_cases i
    · exact hc k h
    · exact absurd rfl h
  have hdvs : ∀ i k, dv i k ≠ 0 → k ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ∧ Even (k + ℓ) := by
    intro i k h; fin_cases i
    · exact hd k h
    · exact absurd rfl h
  obtain ⟨c', hc', hT⟩ := expansion_eq_T ℓ cv hcvs
  obtain ⟨a, ha, haeq⟩ := pairing_integer_frequencies ℓ c' dv hc' hdvs 1
  refine ⟨a, ha, fun x => ?_⟩
  rw [← haeq x, ← hT x, Matrix.one_mulVec]
  simp [ip, hcv, hdv, hcx, hdx]

theorem trig_finset_sum {ι : Type*} (L : ℕ) (s : Finset ι) (a : ι → ℤ → ℂ) (x : ℝ) :
    trig L (fun k => ∑ i ∈ s, a i k) x = ∑ i ∈ s, trig L (a i) x := by
  unfold trig
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- Every amplitude of the ancilla state is a half-integer expansion of degree `L`. -/
theorem ancillaState_halfExp :
    ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p : Fin 2 × Fin 2),
      HalfExp L (fun x => ancillaState L W x p)
  | 0, W, p => by
    refine (HalfExp.const ((W 0 *ᵥ ket00) p)).congr fun x => ?_
    rfl
  | L + 1, W, p => by
    have ih := ancillaState_halfExp L (fun i => W (Fin.castSucc i))
    have hin : ∀ q, HalfExp (L + 1) (fun x => (Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        ancillaState L (fun i => W (Fin.castSucc i)) x) q) := by
      intro q
      refine (HalfExp.sum Finset.univ (fun q' x => (1 : Matrix (Fin 2) (Fin 2) ℂ) q.2 q'.2 *
        (RXm x q.1 q'.1 * ancillaState L (fun i => W (Fin.castSucc i)) x q'))
        fun q' _ => ((ih q').RX q.1 q'.1).const_mul _).congr fun x => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact Finset.sum_congr rfl fun q' _ => by ring
    refine (HalfExp.sum Finset.univ (fun q x => W (Fin.last (L + 1)) p q *
      (Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        ancillaState L (fun i => W (Fin.castSucc i)) x) q) fun q _ => (hin q).const_mul _).congr fun x => ?_
    rfl

/-- The readout `I ⊗ Z` acts diagonally with signs `±1`. -/
theorem kronZ_mulVec (v : Fin 2 × Fin 2 → ℂ) (p : Fin 2 × Fin 2) :
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ v) p = (if p.2 = 0 then 1 else -1) * v p := by
  obtain ⟨a, b⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp [Zm, Matrix.one_apply]

/-- The ancilla output as a real sum of signed squared moduli. -/
theorem ancillaModel_eq (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    ((ancillaModel L W x : ℝ) : ℂ) = ∑ p, (starRingEnd ℂ) (ancillaState L W x p) *
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) p := by
  have hsum : ∑ p, (starRingEnd ℂ) (ancillaState L W x p) *
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) p =
      ((∑ p, (if p.2 = 0 then (1 : ℝ) else -1) * Complex.normSq (ancillaState L W x p) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [kronZ_mulVec, Complex.normSq_eq_conj_mul_self]
    split_ifs <;> push_cast <;> ring
  rw [hsum]
  congr 1
  unfold ancillaModel
  have : dotProduct (star (ancillaState L W x))
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) =
      ∑ p, (starRingEnd ℂ) (ancillaState L W x p) *
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) p := rfl
  rw [this, hsum, Complex.ofReal_re]

/-- The ancilla output as a real sum of signed squared moduli. -/
theorem ancillaModel_eq_real (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    ancillaModel L W x = ∑ p, (if p.2 = 0 then (1 : ℝ) else -1) * Complex.normSq (ancillaState L W x p) := by
  have h := ancillaModel_eq L W x
  have hsum : ∑ p, (starRingEnd ℂ) (ancillaState L W x p) *
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) p =
      ((∑ p, (if p.2 = 0 then (1 : ℝ) else -1) * Complex.normSq (ancillaState L W x p) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [kronZ_mulVec, Complex.normSq_eq_conj_mul_self]
    split_ifs <;> push_cast <;> ring
  rw [hsum] at h
  exact_mod_cast h

theorem star_dotProduct_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [show Uᴴ * U = 1 from (Matrix.mem_unitaryGroup_iff').1 hU, Matrix.one_mulVec]

theorem ancillaState_norm :
    ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      (∀ ℓ, W ℓ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) → ∀ x,
      star (ancillaState L W x) ⬝ᵥ ancillaState L W x = 1
  | 0, W, hW, x => by
    show star (W 0 *ᵥ ket00) ⬝ᵥ (W 0 *ᵥ ket00) = 1
    rw [star_dotProduct_unitary _ (hW 0)]
    simp [dotProduct, ket00]
  | L + 1, W, hW, x => by
    show star (W (Fin.last (L + 1)) *ᵥ _) ⬝ᵥ (W (Fin.last (L + 1)) *ᵥ _) = 1
    rw [star_dotProduct_unitary _ (hW _),
      star_dotProduct_unitary _ (kron_one_mem_SU4 _ (RXm_mem_SU2 x)).1]
    exact ancillaState_norm L _ (fun ℓ => hW _) x

/-- The ancilla output is bounded by `‖Z‖ = 1` for unitary blocks. -/
theorem ancillaModel_abs_le_one (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hW : ∀ ℓ, W ℓ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) (x : ℝ) : |ancillaModel L W x| ≤ 1 := by
  rw [ancillaModel_eq_real]
  have hn : ∑ p, Complex.normSq (ancillaState L W x p) = 1 := by
    have h := ancillaState_norm L W hW x
    have h2 : star (ancillaState L W x) ⬝ᵥ ancillaState L W x =
        ((∑ p, Complex.normSq (ancillaState L W x p) : ℝ) : ℂ) := by
      rw [dotProduct]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Pi.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [h2] at h
    exact_mod_cast h
  calc |∑ p, (if p.2 = 0 then (1 : ℝ) else -1) * Complex.normSq (ancillaState L W x p)|
      ≤ ∑ p, |(if p.2 = 0 then (1 : ℝ) else -1) * Complex.normSq (ancillaState L W x p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p, Complex.normSq (ancillaState L W x p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
        split_ifs <;> simp
    _ = 1 := hn

/-- The ancilla output is a trigonometric polynomial of degree ≤ L (for any blocks). -/
theorem ancillaModel_trig (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∃ c : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0) ∧
      ∀ x, ((ancillaModel L W x : ℝ) : ℂ) = trig L c x := by
  have hpair : ∀ p : Fin 2 × Fin 2, ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
      ∀ x, (starRingEnd ℂ) (ancillaState L W x p) *
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L W x) p = trig L a x := by
    intro p
    refine (ancillaState_halfExp L W p).pair ?_
    refine (HalfExp.sum Finset.univ (fun q x => Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm p q *
      ancillaState L W x q) fun q _ => (ancillaState_halfExp L W q).const_mul _).congr fun x => ?_
    rfl
  choose a ha haeq using hpair
  refine ⟨fun k => ∑ p, a p k, fun k hk => Finset.sum_eq_zero fun p _ => ha p k hk, fun x => ?_⟩
  rw [ancillaModel_eq, trig_finset_sum]
  exact Finset.sum_congr rfl fun p _ => haeq p x

/-- The ancilla circuit with `L+1` blocks of `tbl` SU(4) gates. -/
def ancillaGateModel (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) : ℝ :=
  ancillaModel L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x

/-- Non-identity Pauli words on two qubits. -/
abbrev PWord := {p : Fin 4 × Fin 4 // p ≠ (0, 0)}

def pauliWord (p : PWord) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (pauli1 p.1.1) (pauli1 p.1.2)

def ancillaCoeffVec (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Fin (2 * L + 1) → ℝ :=
  realRep L (realFourierCoeff (ancillaGateModel L tbl G))

abbrev AIdx (L tbl : ℕ) := Fin (L + 1) × Fin tbl × PWord

/-- Coefficient Jacobian of the ancilla circuit in Lie-algebra coordinates (Definition 3.2). -/
def ancillaJ (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Matrix (Fin (2 * L + 1)) (AIdx L tbl) ℝ :=
  fun r j => deriv (fun s => ancillaCoeffVec L tbl
    (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) r) 0

/-- Amplitudes of the ancilla state depend differentiably on differentiable blocks. -/
theorem ancillaState_differentiableAt :
    ∀ (L : ℕ) (V : ℝ → Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      (∀ ℓ a b, DifferentiableAt ℝ (fun s => V s ℓ a b) 0) → ∀ x p,
      DifferentiableAt ℝ (fun s => ancillaState L (V s) x p) 0
  | 0, V, hV, x, p => by
    show DifferentiableAt ℝ (fun s => ∑ q, V s 0 p q * ket00 q) 0
    exact DifferentiableAt.fun_sum fun q _ => (hV 0 p q).mul_const _
  | L + 1, V, hV, x, p => by
    show DifferentiableAt ℝ (fun s => ∑ q, V s (Fin.last (L + 1)) p q *
      (Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        ancillaState L (fun i => V s (Fin.castSucc i)) x) q) 0
    refine DifferentiableAt.fun_sum fun q _ => (hV _ p q).mul ?_
    show DifferentiableAt ℝ (fun s => ∑ q', Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) q q' *
      ancillaState L (fun i => V s (Fin.castSucc i)) x q') 0
    exact DifferentiableAt.fun_sum fun q' _ =>
      (ancillaState_differentiableAt L _ (fun ℓ => hV _) x q').const_mul _

/-- The ancilla output along a coordinate curve is differentiable. -/
theorem ancillaGateModel_differentiableAt (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (i : Fin (L + 1) × Fin tbl) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    DifferentiableAt ℝ (fun s => ancillaGateModel L tbl (perturb G i (lieCurve (G i) P s)) x) 0 := by
  obtain ⟨U, D, -, -, hUD⟩ := gate_blocks_update G i
  have hV : ∀ ℓ a b, DifferentiableAt ℝ (fun s => Function.update
      (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) i.1 (U * lieCurve (G i) P s * D) ℓ a b) 0 := by
    intro ℓ a b
    by_cases hℓ : ℓ = i.1
    · subst hℓ
      simp only [Function.update_self, Matrix.mul_apply]
      refine DifferentiableAt.fun_sum fun c _ => DifferentiableAt.mul_const ?_ _
      exact DifferentiableAt.fun_sum fun e _ =>
        ((lieCurve_hasDerivAt (G i) P e c).differentiableAt).const_mul _
    · simp only [Function.update_of_ne hℓ]
      exact differentiableAt_const _
  have hst := ancillaState_differentiableAt L _ hV x
  unfold ancillaGateModel
  simp_rw [hUD]
  unfold ancillaModel
  have hre : ∀ z : ℂ, z.re = Complex.reCLM z := fun z => rfl
  simp_rw [hre]
  refine Complex.reCLM.differentiableAt.comp 0 ?_
  simp only [dotProduct, Pi.star_apply]
  refine DifferentiableAt.fun_sum fun p _ => DifferentiableAt.mul ?_ ?_
  · exact ((hst p).hasDerivAt.star).differentiableAt
  · simp only [Matrix.mulVec, dotProduct]
    exact DifferentiableAt.fun_sum fun q _ => (hst q).const_mul _

theorem ancilla_model_eq_design (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) :
    ancillaGateModel L tbl G x = ∑ r, designEntry L x r * ancillaCoeffVec L tbl G r := by
  obtain ⟨c, hc, hcx⟩ := ancillaModel_trig L (fun ℓ => blockProd tbl (fun g => G (ℓ, g)))
  exact design_form_of_trig L c hc _ hcx x

theorem ancillaCoeffVec_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl)
    (r : Fin (2 * L + 1)) :
    HasDerivAt (fun s => ancillaCoeffVec L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) r) (ancillaJ L tbl G r j) 0 := by
  set Gs : ℝ → Gates L tbl (Fin 2 × Fin 2) :=
    fun s => perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s) with hGs
  set B := designMatrix L (eqGrid L 0) with hB
  have hrep : ∀ s, ancillaCoeffVec L tbl (Gs s) =
      B⁻¹ *ᵥ (fun k => ancillaGateModel L tbl (Gs s) (eqGrid L 0 k)) := by
    intro s
    conv_lhs => rw [vec_eq_design_inv L 0 (ancillaCoeffVec L tbl (Gs s))]
    congr 1
    funext k
    rw [ancilla_model_eq_design]
  have hd : DifferentiableAt ℝ (fun s => ancillaCoeffVec L tbl (Gs s) r) 0 := by
    have : (fun s => ancillaCoeffVec L tbl (Gs s) r) =
        fun s => ∑ k, B⁻¹ r k * ancillaGateModel L tbl (Gs s) (eqGrid L 0 k) := by
      funext s
      rw [hrep s]
      rfl
    rw [this]
    exact DifferentiableAt.fun_sum fun k _ =>
      (ancillaGateModel_differentiableAt L tbl G _ _ _).const_mul _
  exact hd.hasDerivAt

/-- Lemma B.3 for the ancilla circuit.
    (The hypothesis `hG` is kept as stated in the paper; the proof does not need them.) -/
theorem ancilla_stationary_is_least_squares (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (_hG : InSU G) {n : ℕ}
    (x y : Fin n → ℝ) (hrank : (ancillaJ L tbl G).rank = 2 * L + 1)
    (hstat : ∀ j : AIdx L tbl, HasDerivAt (fun s => (1 / n : ℝ) * ∑ i,
      (ancillaGateModel L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) (x i)
        - y i) ^ 2) 0 0)
    (c' : Fin (2 * L + 1) → ℝ) :
    (1 / n : ℝ) * ∑ i, (ancillaGateModel L tbl G (x i) - y i) ^ 2 ≤
      (1 / n : ℝ) * ∑ i, ((designMatrix L x *ᵥ c') i - y i) ^ 2 := by
  have h := stationary_is_least_squares L
    (fun (j : AIdx L tbl) s x =>
      ancillaGateModel L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) x)
    (fun j s => ancillaCoeffVec L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)))
    (fun j s x => ancilla_model_eq_design L tbl _ x) (ancillaJ L tbl G)
    (fun j r => ancillaCoeffVec_hasDerivAt L tbl G j r) (ancillaCoeffVec L tbl G)
    (fun j => by simp only [lieCurve_zero, perturb_self]) x y hrank hstat c'
  have hl : ∀ i, ancillaGateModel L tbl G (x i) = (designMatrix L x *ᵥ ancillaCoeffVec L tbl G) i := by
    intro i
    rw [ancilla_model_eq_design]
    simp [mulVec, dotProduct, designEntry, designMatrix]
  simp_rw [hl]
  exact h

end

end


/-! # Section 18: Lemma 3.3(i) (model classes), and polynomial dependence on the gate entries -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 18. Lemma 3.3(i): model classes -/

/-- `F_E`: real trigonometric polynomials of degree ≤ L with sup-norm ≤ 1. -/
def FE (L : ℕ) : Set (ℝ → ℝ) :=
  {f | ∃ c : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → c k = 0) ∧ (∀ x, ((f x : ℝ) : ℂ) = trig L c x) ∧
    ∀ x, |f x| ≤ 1}

def serialClass (L tbl : ℕ) : Set (ℝ → ℝ) := {f | ∃ G : Gates L tbl (Fin 2), InSU G ∧ f = gateModel L tbl G}

def ancillaClass (L tbl : ℕ) : Set (ℝ → ℝ) :=
  {f | ∃ G : Gates L tbl (Fin 2 × Fin 2), InSU G ∧ f = ancillaGateModel L tbl G}

/-- A block whose first gate is `A` and whose other gates are the identity is `A`. -/
theorem blockProd_single {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ∀ t : ℕ, blockProd (t + 1) (fun g => if (g : ℕ) = 0 then A else 1) = A
  | 0 => by simp [blockProd]
  | t + 1 => by
    rw [blockProd]
    have h := blockProd_single A t
    simp only [Fin.val_last, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, one_mul,
      Fin.val_castSucc]
    exact h

/-- Gates realising given blocks: block `ℓ` has first gate `V ℓ`, all other gates the identity. -/
def singleGates (L tbl : ℕ) {n : Type*} [DecidableEq n] (V : Fin (L + 1) → Matrix n n ℂ) : Gates L tbl n :=
  fun i => if (i.2 : ℕ) = 0 then V i.1 else 1

theorem singleGates_blockProd (L tbl : ℕ) (htbl : 1 ≤ tbl) {n : Type*} [Fintype n] [DecidableEq n]
    (V : Fin (L + 1) → Matrix n n ℂ) (ℓ : Fin (L + 1)) :
    blockProd tbl (fun g => singleGates L tbl V (ℓ, g)) = V ℓ := by
  obtain ⟨t, rfl⟩ : ∃ t, tbl = t + 1 := ⟨tbl - 1, by omega⟩
  exact blockProd_single (V ℓ) t

theorem singleGates_InSU (L tbl : ℕ) {n : Type*} [Fintype n] [DecidableEq n] (V : Fin (L + 1) → Matrix n n ℂ)
    (hV : ∀ ℓ, V ℓ ∈ Matrix.specialUnitaryGroup n ℂ) : InSU (singleGates L tbl V) := by
  intro i
  unfold singleGates
  split_ifs
  · exact hV _
  · exact one_mem _

/-- The serial output as a difference of populations. -/
theorem ip_Zm_re (ψ : Fin 2 → ℂ) :
    (ip ψ (Zm *ᵥ ψ)).re = Complex.normSq (ψ 0) - Complex.normSq (ψ 1) := by
  simp [ip, Zm, mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem ip_self_re (ψ : Fin 2 → ℂ) :
    (ip ψ ψ).re = Complex.normSq (ψ 0) + Complex.normSq (ψ 1) := by
  simp [ip, Complex.normSq_apply]

/-- The serial output is bounded by one. -/
theorem gateModel_abs_le_one (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (x : ℝ) :
    |gateModel L tbl G x| ≤ 1 := by
  have h := congrArg Complex.re (gateState_normalised L tbl G (fun i => (hG i).1) x)
  rw [ip_self_re, Complex.one_re] at h
  unfold gateModel
  rw [ip_Zm_re, abs_le]
  have h0 := Complex.normSq_nonneg (gateState L tbl G x 0)
  have h1 := Complex.normSq_nonneg (gateState L tbl G x 1)
  constructor <;> linarith

/-- The basis change `K = R_Y(−π/2)` with `K R_X(x) K⁻¹ = R_Z(x)`. -/
def Kmat : Matrix (Fin 2) (Fin 2) ℂ := RY (-(Real.pi / 2))

theorem Kmat_mem_SU2 : Kmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := RY_mem_SU2 _

theorem Kmat_entries :
    Kmat = !![((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ);
      -((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ)] := by
  have hc : Real.cos (-(Real.pi / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
  have hs : Real.sin (-(Real.pi / 2) / 2) = -(Real.sqrt 2 / 2) := by
    rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.sin_neg, Real.sin_pi_div_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Kmat, RY, hc, hs]

/-- The signal operator is, up to a phase, `R_X` in the `K` basis. -/
theorem sigMat_eq (x : ℝ) :
    sigMat x = Complex.exp (Complex.I * (x : ℂ) / 2) • (Kmat * RXm x * star Kmat) := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  set E := Complex.exp (Complex.I * (x : ℂ) / 2) with hE
  set C := Complex.cos ((x : ℂ) / 2) with hC
  set S := Complex.sin ((x : ℂ) / 2) with hS
  have h1 : E * (C - S * Complex.I) = 1 := by
    rw [hC, hS, Complex.cos_sub_sin_I, hE, ← Complex.exp_add]
    rw [show Complex.I * (x : ℂ) / 2 + -((x : ℂ) / 2) * Complex.I = 0 by ring, Complex.exp_zero]
  have h2 : E * (C + S * Complex.I) = Complex.exp (Complex.I * (x : ℂ)) := by
    rw [hC, hS, Complex.cos_add_sin_I, hE, ← Complex.exp_add]
    congr 1; ring
  have hstar : star (!![((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ);
      -((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ)]) =
      !![((Real.sqrt 2 / 2 : ℝ) : ℂ), -((Real.sqrt 2 / 2 : ℝ) : ℂ);
      ((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  rw [Kmat_entries, hstar, RXm, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigMat, ← hC, ← hS] <;>
    first
      | (right; ring)
      | linear_combination (-1 : ℂ) * h1 - E * (C - S * Complex.I) / 2 * hs2
      | linear_combination (-1 : ℂ) * h2 - E * (C + S * Complex.I) / 2 * hs2

theorem Kstar_mem_SU2 : star Kmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (star (⟨Kmat, Kmat_mem_SU2⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ)).2

/-- Serial blocks realising a signal-processing sequence `U`: `U_L K, K⁻¹ U_ℓ K, …, K⁻¹ U_0`. -/
def gqspBlocks (L : ℕ) (U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun ℓ => (if ℓ = Fin.last L then U ℓ else star Kmat * U ℓ) * (if (ℓ : ℕ) = 0 then 1 else Kmat)

theorem gqspBlocks_mem (L : ℕ) (U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ ℓ, U ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (ℓ : Fin (L + 1)) :
    gqspBlocks L U ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold gqspBlocks
  refine mul_mem ?_ ?_
  · split_ifs
    · exact hU ℓ
    · exact mul_mem Kstar_mem_SU2 (hU ℓ)
  · split_ifs
    · exact one_mem _
    · exact Kmat_mem_SU2

theorem sigState_aux (x : ℝ) : ∀ (L : ℕ) (U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ),
    star Kmat *ᵥ sigState L U x = Complex.exp (Complex.I * (x : ℂ) / 2) ^ L •
      serialState L (fun ℓ => star Kmat * U ℓ * (if (ℓ : ℕ) = 0 then 1 else Kmat)) x
  | 0, U => by simp [sigState, serialState, mulVec_mulVec]
  | L + 1, U => by
    have ih := sigState_aux x L (fun i => U (Fin.castSucc i))
    have hV : (fun i : Fin (L + 1) => (fun ℓ : Fin (L + 2) => star Kmat * U ℓ *
        (if (ℓ : ℕ) = 0 then 1 else Kmat)) (Fin.castSucc i)) =
        fun i => star Kmat * U (Fin.castSucc i) * (if (i : ℕ) = 0 then 1 else Kmat) := by
      funext i; simp
    have e : ∀ v : Fin 2 → ℂ, star Kmat *ᵥ (U (Fin.last (L + 1)) *ᵥ (sigMat x *ᵥ v)) =
        Complex.exp (Complex.I * (x : ℂ) / 2) • ((star Kmat * U (Fin.last (L + 1)) * Kmat) *ᵥ
          (RXm x *ᵥ (star Kmat *ᵥ v))) := by
      intro v
      rw [sigMat_eq]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, mulVec_mulVec, Matrix.mul_assoc]
    simp only [sigState, serialState, hV]
    rw [e, ih, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, pow_succ, mul_comm]
    simp
theorem sigState_eq_serial (x : ℝ) (L : ℕ) (U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    sigState L U x = Complex.exp (Complex.I * (x : ℂ) / 2) ^ L • serialState L (gqspBlocks L U) x := by
  cases L with
  | zero => simp [sigState, serialState, gqspBlocks]
  | succ L =>
    have ih := sigState_aux x L (fun i => U (Fin.castSucc i))
    have hV : (fun i : Fin (L + 1) => gqspBlocks (L + 1) U (Fin.castSucc i)) =
        fun i => star Kmat * U (Fin.castSucc i) * (if (i : ℕ) = 0 then 1 else Kmat) := by
      funext i; simp [gqspBlocks, (Fin.castSucc_lt_last i).ne, Matrix.mul_assoc]
    have hL : gqspBlocks (L + 1) U (Fin.last (L + 1)) = U (Fin.last (L + 1)) * Kmat := by
      simp [gqspBlocks]
    have e : ∀ v : Fin 2 → ℂ, U (Fin.last (L + 1)) *ᵥ (sigMat x *ᵥ v) =
        Complex.exp (Complex.I * (x : ℂ) / 2) • ((U (Fin.last (L + 1)) * Kmat) *ᵥ
          (RXm x *ᵥ (star Kmat *ᵥ v))) := by
      intro v
      rw [sigMat_eq]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, mulVec_mulVec, Matrix.mul_assoc]
    simp only [sigState, serialState, hV, hL]
    rw [e, ih, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, pow_succ, mul_comm]

/-- Output of a state that is a unit-modulus multiple of `(P, Q)`. -/
theorem ip_Zm_re_smul (a : ℂ) (ha : ‖a‖ = 1) (ψ : Fin 2 → ℂ) :
    (ip (a • ψ) (Zm *ᵥ (a • ψ))).re = (ip ψ (Zm *ᵥ ψ)).re := by
  have h : Complex.normSq a = 1 := by rw [Complex.normSq_eq_norm_sq, ha]; norm_num
  rw [ip_Zm_re, ip_Zm_re]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, h, one_mul]

theorem norm_exp_half (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ) / 2)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **Lemma 3.3(i), serial.** -/
theorem serial_class_eq (hFR : FejerRieszHyp) (hQ : GQSPHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    serialClass L tbl = FE L := by
  apply Set.Subset.antisymm
  · rintro f ⟨G, hG, rfl⟩
    obtain ⟨c, hc, hceq⟩ := gateModel_trig L tbl G
    exact ⟨c, hc, hceq, gateModel_abs_le_one L tbl G hG⟩
  · rintro f ⟨c, hc, hceq, hbd⟩
    set δ : ℤ → ℂ := fun k => if k = 0 then 1 else 0 with hδdef
    have hδ : ∀ x, trig L δ x = 1 := by
      intro x
      simp [trig, hδdef]
    have hlin : ∀ (s : ℂ) x, trig L (fun k => δ k / 2 + s * (c k / 2)) x = (1 + s * (f x : ℂ)) / 2 := by
      intro s x
      have : trig L (fun k => δ k / 2 + s * (c k / 2)) x = trig L δ x / 2 + s * (trig L c x / 2) := by
        simp only [trig, add_mul, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
      rw [this, hδ, ← hceq]; ring
    have hsupp : ∀ s : ℂ, ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → δ k / 2 + s * (c k / 2) = 0 := by
      intro s k hk
      have hk0 : k ≠ 0 := by rintro rfl; exact hk (by simp)
      simp [hδdef, hk0, hc k hk]
    have hbd' := fun x => abs_le.1 (hbd x)
    obtain ⟨p, hp, hpeq⟩ := hFR L _ (hsupp 1) (fun x => by
      rw [hlin]; constructor
      · simp
      · simp; linarith [(hbd' x).1])
    obtain ⟨q, hq, hqeq⟩ := hFR L _ (hsupp (-1)) (fun x => by
      rw [hlin]; constructor
      · simp
      · simp; linarith [(hbd' x).2])
    have hP : ∀ x, Complex.normSq (trig L p x) = (1 + f x) / 2 := by
      intro x
      have h := (hpeq x).symm
      rw [hlin] at h
      exact_mod_cast (by rw [h]; push_cast; ring : ((Complex.normSq (trig L p x) : ℝ) : ℂ) = (((1 + f x) / 2 : ℝ) : ℂ))
    have hQ' : ∀ x, Complex.normSq (trig L q x) = (1 - f x) / 2 := by
      intro x
      have h := (hqeq x).symm
      rw [hlin] at h
      exact_mod_cast (by rw [h]; push_cast; ring : ((Complex.normSq (trig L q x) : ℝ) : ℂ) = (((1 - f x) / 2 : ℝ) : ℂ))
    obtain ⟨U, hU, φ, hφ, hUeq⟩ := hQ L p q hp hq (fun x => by rw [hP, hQ']; ring)
    refine ⟨singleGates L tbl (gqspBlocks L U), singleGates_InSU _ _ _ (gqspBlocks_mem L U hU), ?_⟩
    funext x
    have hgs : gateState L tbl (singleGates L tbl (gqspBlocks L U)) x = serialState L (gqspBlocks L U) x := by
      unfold gateState
      congr 1
      funext ℓ
      exact singleGates_blockProd L tbl htbl _ ℓ
    have hE : ‖Complex.exp (Complex.I * (x : ℂ) / 2) ^ L‖ = 1 := by rw [norm_pow, norm_exp_half, one_pow]
    unfold gateModel
    rw [hgs, ← ip_Zm_re_smul _ hE, ← sigState_eq_serial, hUeq x, ip_Zm_re_smul φ hφ, ip_Zm_re]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hP, hQ']
    ring

/-- `ψ ⊗ e₀`. -/
def kvec (ψ : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => if p.2 = 0 then ψ p.1 else 0

theorem kron_one_kvec (A : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ) :
    Matrix.kronecker A 1 *ᵥ kvec ψ = kvec (A *ᵥ ψ) := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, kvec]
  fin_cases b <;> simp [Matrix.one_apply]

theorem ancillaState_kron (x : ℝ) : ∀ (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ),
    ancillaState L (fun ℓ => Matrix.kronecker (V ℓ) 1) x = kvec (serialState L V x)
  | 0, V => by
    have hk : ket00 = kvec ![1, 0] := by
      funext p; obtain ⟨a, b⟩ := p
      fin_cases a <;> fin_cases b <;> simp [ket00, kvec]
    show Matrix.kronecker (V 0) 1 *ᵥ ket00 = kvec (V 0 *ᵥ ![1, 0])
    rw [hk, kron_one_kvec]
  | L + 1, V => by
    have ih := ancillaState_kron x L (fun i => V (Fin.castSucc i))
    show Matrix.kronecker (V (Fin.last (L + 1))) 1 *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
      ancillaState L (fun i => Matrix.kronecker (V (Fin.castSucc i)) 1) x) = _
    rw [ih, kron_one_kvec, kron_one_kvec]
    rfl

theorem ancillaState_embed (x : ℝ) (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    ancillaState L (ancillaEmbed L V) x =
      (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • swapGate) *ᵥ kvec (serialState L V x) := by
  cases L with
  | zero =>
    have h := ancillaState_kron x 0 V
    show ancillaEmbed 0 V 0 *ᵥ ket00 = _
    have h0 : ancillaEmbed 0 V 0 = (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • swapGate) *
        Matrix.kronecker (V 0) 1 := by simp [ancillaEmbed]
    rw [h0, ← mulVec_mulVec]
    rw [← h]
    rfl
  | succ L =>
    have hc : (fun i : Fin (L + 1) => ancillaEmbed (L + 1) V (Fin.castSucc i)) =
        fun i => Matrix.kronecker (V (Fin.castSucc i)) 1 := by
      funext i; simp [ancillaEmbed, (Fin.castSucc_lt_last i).ne]
    have hl : ancillaEmbed (L + 1) V (Fin.last (L + 1)) =
        (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • swapGate) *
          Matrix.kronecker (V (Fin.last (L + 1))) 1 := by simp [ancillaEmbed]
    show ancillaEmbed (L + 1) V (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
      ancillaState L (fun i => ancillaEmbed (L + 1) V (Fin.castSucc i)) x) = _
    rw [hc, ancillaState_kron x L (fun i => V (Fin.castSucc i)), kron_one_kvec, hl, ← mulVec_mulVec,
      kron_one_kvec]
    rfl

/-- The embedded ancilla circuit reproduces the serial output, for any blocks. -/
theorem ancillaModel_embed (x : ℝ) (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    ancillaModel L (ancillaEmbed L V) x = (ip (serialState L V x) (Zm *ᵥ serialState L V x)).re := by
  rw [ancillaModel_eq_real, ancillaState_embed, ip_Zm_re]
  have hc : Complex.normSq (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]; simp
  have hs : ∀ (v : Fin 2 × Fin 2 → ℂ) (p : Fin 2 × Fin 2), (swapGate *ᵥ v) p = v (p.2, p.1) := by
    intro v p
    simp only [Matrix.mulVec, dotProduct, swapGate]
    rw [Finset.sum_eq_single (p.2, p.1)]
    · simp
    · intro q _ hq
      rw [if_neg]
      · simp
      · intro h; apply hq; rw [h]
    · simp
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, hc, one_mul, hs, kvec,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp
  ring

/-- **Lemma 3.3(i), ancilla.** -/
theorem ancilla_class_eq (hFR : FejerRieszHyp) (hQ : GQSPHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    ancillaClass L tbl = FE L := by
  apply Set.Subset.antisymm
  · rintro f ⟨G, hG, rfl⟩
    obtain ⟨c, hc, hceq⟩ := ancillaModel_trig L (fun ℓ => blockProd tbl (fun g => G (ℓ, g)))
    exact ⟨c, hc, hceq, ancillaModel_abs_le_one L _
      (fun ℓ => blockProd_mem (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) tbl _ fun g => (hG _).1)⟩
  · intro f hf
    rw [← serial_class_eq hFR hQ L 1 le_rfl] at hf
    obtain ⟨G, hG, rfl⟩ := hf
    set V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ := fun ℓ => blockProd 1 (fun g => G (ℓ, g)) with hV
    have hVmem : ∀ ℓ, V ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := fun ℓ =>
      blockProd_mem (Matrix.specialUnitaryGroup (Fin 2) ℂ) 1 _ fun g => hG _
    refine ⟨singleGates L tbl (ancillaEmbed L V),
      singleGates_InSU _ _ _ (ancillaEmbed_mem_SU4 L V hVmem), ?_⟩
    funext x
    unfold ancillaGateModel
    rw [show (fun ℓ => blockProd tbl (fun g => singleGates L tbl (ancillaEmbed L V) (ℓ, g))) =
      ancillaEmbed L V from funext fun ℓ => singleGates_blockProd L tbl htbl _ ℓ, ancillaModel_embed]
    rfl

end

end


/-! ### Polynomial dependence on the gate entries (used for Lemma 3.3(ii)) -/

@[expose] public section

open Matrix

set_option autoImplicit false

noncomputable section

section PolyFn

variable {ι n : Type*}

/-- A real function of the gates that is a real polynomial in the real and imaginary parts of the entries. -/
def IsRPoly (F : (ι → Matrix n n ℂ) → ℝ) : Prop :=
  ∃ q : MvPolynomial (ι × n × n × Bool) ℝ, ∀ G, F G = MvPolynomial.eval (reIm G) q

/-- A complex function of the gates whose real and imaginary parts are real polynomials in the entries. -/
def IsCPoly (F : (ι → Matrix n n ℂ) → ℂ) : Prop :=
  IsRPoly (fun G => (F G).re) ∧ IsRPoly (fun G => (F G).im)

theorem IsRPoly.const (r : ℝ) : IsRPoly (fun _ : ι → Matrix n n ℂ => r) :=
  ⟨MvPolynomial.C r, fun G => by simp⟩

theorem IsRPoly.add {F F' : (ι → Matrix n n ℂ) → ℝ} (h : IsRPoly F) (h' : IsRPoly F') :
    IsRPoly (fun G => F G + F' G) := by
  obtain ⟨q, hq⟩ := h; obtain ⟨q', hq'⟩ := h'
  exact ⟨q + q', fun G => by simp [hq, hq']⟩

theorem IsRPoly.mul {F F' : (ι → Matrix n n ℂ) → ℝ} (h : IsRPoly F) (h' : IsRPoly F') :
    IsRPoly (fun G => F G * F' G) := by
  obtain ⟨q, hq⟩ := h; obtain ⟨q', hq'⟩ := h'
  exact ⟨q * q', fun G => by simp [hq, hq']⟩

theorem IsRPoly.neg {F : (ι → Matrix n n ℂ) → ℝ} (h : IsRPoly F) : IsRPoly (fun G => -F G) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨-q, fun G => by simp [hq]⟩

theorem IsRPoly.sub {F F' : (ι → Matrix n n ℂ) → ℝ} (h : IsRPoly F) (h' : IsRPoly F') :
    IsRPoly (fun G => F G - F' G) := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem IsRPoly.congr {F F' : (ι → Matrix n n ℂ) → ℝ} (h : IsRPoly F) (e : ∀ G, F G = F' G) : IsRPoly F' := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, fun G => by rw [← e, hq]⟩

theorem IsRPoly.sum {κ : Type*} (s : Finset κ) {F : κ → (ι → Matrix n n ℂ) → ℝ}
    (h : ∀ k ∈ s, IsRPoly (F k)) : IsRPoly (fun G => ∑ k ∈ s, F k G) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRPoly.const (ι := ι) (n := n) 0
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact (h1.add h2).congr fun G => by rw [Finset.sum_insert ha]

theorem IsRPoly.prod {κ : Type*} (s : Finset κ) {F : κ → (ι → Matrix n n ℂ) → ℝ}
    (h : ∀ k ∈ s, IsRPoly (F k)) : IsRPoly (fun G => ∏ k ∈ s, F k G) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRPoly.const (ι := ι) (n := n) 1
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact (h1.mul h2).congr fun G => by rw [Finset.prod_insert ha]

/-- The determinant of a matrix of polynomial functions is a polynomial function. -/
theorem IsRPoly.det {m : Type*} [Fintype m] [DecidableEq m] (M : (ι → Matrix n n ℂ) → Matrix m m ℝ)
    (h : ∀ a b, IsRPoly (fun G => M G a b)) : IsRPoly (fun G => (M G).det) := by
  refine (IsRPoly.sum Finset.univ (F := fun σ G => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ i, M G (σ i) i) fun σ _ => ?_).congr fun G => ?_
  · exact (IsRPoly.const _).mul (IsRPoly.prod _ fun i _ => h _ _)
  · rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]

theorem IsCPoly.const (z : ℂ) : IsCPoly (fun _ : ι → Matrix n n ℂ => z) :=
  ⟨IsRPoly.const _, IsRPoly.const _⟩

theorem IsCPoly.entry (i : ι) (a b : n) : IsCPoly (fun G : ι → Matrix n n ℂ => G i a b) :=
  ⟨⟨MvPolynomial.X (i, a, b, true), fun G => by simp [reIm]⟩,
    ⟨MvPolynomial.X (i, a, b, false), fun G => by simp [reIm]⟩⟩

theorem IsCPoly.add {F F' : (ι → Matrix n n ℂ) → ℂ} (h : IsCPoly F) (h' : IsCPoly F') :
    IsCPoly (fun G => F G + F' G) :=
  ⟨(h.1.add h'.1).congr fun G => by simp, (h.2.add h'.2).congr fun G => by simp⟩

theorem IsCPoly.mul {F F' : (ι → Matrix n n ℂ) → ℂ} (h : IsCPoly F) (h' : IsCPoly F') :
    IsCPoly (fun G => F G * F' G) :=
  ⟨((h.1.mul h'.1).sub (h.2.mul h'.2)).congr fun G => by simp [Complex.mul_re],
    ((h.1.mul h'.2).add (h.2.mul h'.1)).congr fun G => by simp [Complex.mul_im]⟩

theorem IsCPoly.conj {F : (ι → Matrix n n ℂ) → ℂ} (h : IsCPoly F) :
    IsCPoly (fun G => (starRingEnd ℂ) (F G)) :=
  ⟨h.1.congr fun G => by simp, h.2.neg.congr fun G => by simp⟩

theorem IsCPoly.congr {F F' : (ι → Matrix n n ℂ) → ℂ} (h : IsCPoly F) (e : ∀ G, F G = F' G) : IsCPoly F' :=
  ⟨h.1.congr fun G => by rw [e], h.2.congr fun G => by rw [e]⟩

theorem IsCPoly.sum {κ : Type*} (s : Finset κ) {F : κ → (ι → Matrix n n ℂ) → ℂ}
    (h : ∀ k ∈ s, IsCPoly (F k)) : IsCPoly (fun G => ∑ k ∈ s, F k G) :=
  ⟨(IsRPoly.sum s fun k hk => (h k hk).1).congr fun G => by simp [Complex.re_sum],
    (IsRPoly.sum s fun k hk => (h k hk).2).congr fun G => by simp [Complex.im_sum]⟩

/-- Entries of a product of matrices of polynomial functions. -/
theorem IsCPoly.matMul {m m' m'' : Type*} [Fintype m'] {M : (ι → Matrix n n ℂ) → Matrix m m' ℂ}
    {N : (ι → Matrix n n ℂ) → Matrix m' m'' ℂ} (hM : ∀ a b, IsCPoly (fun G => M G a b))
    (hN : ∀ a b, IsCPoly (fun G => N G a b)) (a : m) (b : m'') : IsCPoly (fun G => (M G * N G) a b) :=
  (IsCPoly.sum Finset.univ fun c _ => (hM a c).mul (hN c b)).congr fun G => by simp [Matrix.mul_apply]

/-- Entries of a matrix-vector product of polynomial functions. -/
theorem IsCPoly.mulVec {m m' : Type*} [Fintype m'] {M : (ι → Matrix n n ℂ) → Matrix m m' ℂ}
    {v : (ι → Matrix n n ℂ) → m' → ℂ} (hM : ∀ a b, IsCPoly (fun G => M G a b))
    (hv : ∀ b, IsCPoly (fun G => v G b)) (a : m) : IsCPoly (fun G => (M G *ᵥ v G) a) :=
  (IsCPoly.sum Finset.univ fun c _ => (hM a c).mul (hv c)).congr fun G => by simp [Matrix.mulVec, dotProduct]

/-- The real part of `⟨u, K v⟩` for polynomial `u`, `v`. -/
theorem IsRPoly.qform {m : Type*} [Fintype m] (K : Matrix m m ℂ) {u v : (ι → Matrix n n ℂ) → m → ℂ}
    (hu : ∀ a, IsCPoly (fun G => u G a)) (hv : ∀ a, IsCPoly (fun G => v G a)) :
    IsRPoly (fun G => (star (u G) ⬝ᵥ (K *ᵥ v G)).re) :=
  ((IsCPoly.sum Finset.univ fun a _ => (hu a).conj.mul
    (IsCPoly.mulVec (M := fun _ => K) (fun a b => IsCPoly.const (K a b)) hv a)).congr fun G => by
      simp [dotProduct]).1

variable [Fintype n] [DecidableEq n]

/-- A block of polynomial gates has polynomial entries. -/
theorem IsCPoly.blockProd : ∀ (t : ℕ) (g : (ι → Matrix n n ℂ) → Fin t → Matrix n n ℂ),
    (∀ j a b, IsCPoly (fun G => g G j a b)) → ∀ a b, IsCPoly (fun G => _root_.blockProd t (g G) a b)
  | 0, g, _, a, b => (IsCPoly.const ((1 : Matrix n n ℂ) a b)).congr fun G => rfl
  | t + 1, g, h, a, b => by
    have := IsCPoly.matMul (h (Fin.last t))
      (IsCPoly.blockProd t (fun G i => g G (Fin.castSucc i)) (fun j => h _)) a b
    exact this.congr fun G => rfl

omit [DecidableEq n] in
/-- Gates with one gate replaced by `G i * A` (for a constant `A`) are polynomial. -/
theorem IsCPoly.perturb_mul {L tbl : ℕ} (i : Fin (L + 1) × Fin tbl) (A : Matrix n n ℂ)
    (j : Fin (L + 1) × Fin tbl) (a b : n) :
    IsCPoly (fun G : Gates L tbl n => perturb G i (G i * A) j a b) := by
  by_cases hj : j = i
  · subst hj
    exact (IsCPoly.matMul (N := fun _ => A) (fun a b => IsCPoly.entry j a b)
      (fun a b => IsCPoly.const (A a b)) a b).congr
      fun G => by simp [perturb]
  · exact (IsCPoly.entry j a b).congr fun G => by simp [perturb, Function.update_of_ne hj]

end PolyFn

/-- Serial states of polynomial blocks are polynomial. -/
theorem IsCPoly.serialState {ι n : Type*} (x : ℝ) (L : ℕ) :
    ∀ (V : (ι → Matrix n n ℂ) → Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ ℓ a b, IsCPoly (fun G => V G ℓ a b)) → ∀ i, IsCPoly (fun G => _root_.serialState L (V G) x i) := by
  induction L with
  | zero =>
    intro V h i
    exact IsCPoly.mulVec (M := fun G => V G 0) (v := fun _ => ![1, 0]) (h 0)
      (fun b => IsCPoly.const _) i
  | succ L ih =>
    intro V h i
    have h1 := ih (fun G ℓ => V G (Fin.castSucc ℓ)) (fun ℓ => h _)
    have h2 := IsCPoly.mulVec (M := fun _ => RXm x) (fun a b => IsCPoly.const (RXm x a b)) h1
    exact IsCPoly.mulVec (M := fun G => V G (Fin.last (L + 1))) (h _) h2 i

/-- Ancilla states of polynomial blocks are polynomial. -/
theorem IsCPoly.ancillaState {ι n : Type*} (x : ℝ) (L : ℕ) :
    ∀ (V : (ι → Matrix n n ℂ) → Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    (∀ ℓ a b, IsCPoly (fun G => V G ℓ a b)) → ∀ i, IsCPoly (fun G => _root_.ancillaState L (V G) x i) := by
  induction L with
  | zero =>
    intro V h i
    exact IsCPoly.mulVec (M := fun G => V G 0) (v := fun _ => ket00) (h 0)
      (fun b => IsCPoly.const _) i
  | succ L ih =>
    intro V h i
    have h1 := ih (fun G ℓ => V G (Fin.castSucc ℓ)) (fun ℓ => h _)
    have h2 := IsCPoly.mulVec (M := fun _ => Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (fun a b => IsCPoly.const _) h1
    exact IsCPoly.mulVec (M := fun G => V G (Fin.last (L + 1))) (h _) h2 i

/-! ### Derivatives along Lie curves -/

/-- The real part of `⟨w, K w⟩` along `w(s) = cos s • u + sin s • v` has derivative `Re⟨u, Kv⟩ + Re⟨v, Ku⟩` at 0. -/
theorem qform_curve_hasDerivAt {m : Type*} [Fintype m] (K : Matrix m m ℂ) (u v : m → ℂ) :
    HasDerivAt (fun s : ℝ => (star ((Real.cos s : ℂ) • u + (Real.sin s : ℂ) • v) ⬝ᵥ
      (K *ᵥ ((Real.cos s : ℂ) • u + (Real.sin s : ℂ) • v))).re)
      ((star u ⬝ᵥ (K *ᵥ v)).re + (star v ⬝ᵥ (K *ᵥ u)).re) 0 := by
  set A := (star u ⬝ᵥ (K *ᵥ u)).re
  set B := (star u ⬝ᵥ (K *ᵥ v)).re + (star v ⬝ᵥ (K *ᵥ u)).re
  set C := (star v ⬝ᵥ (K *ᵥ v)).re
  have e : ∀ s : ℝ, (star ((Real.cos s : ℂ) • u + (Real.sin s : ℂ) • v) ⬝ᵥ
      (K *ᵥ ((Real.cos s : ℂ) • u + (Real.sin s : ℂ) • v))).re =
      Real.cos s ^ 2 * A + Real.cos s * Real.sin s * B + Real.sin s ^ 2 * C := by
    intro s
    have hs : ∀ (r : ℝ) (w : m → ℂ), star ((r : ℂ) • w) = (r : ℂ) • star w := by
      intro r w; rw [star_smul]; simp
    simp only [star_add, hs, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
    simp only [A, B, C]
    ring
  simp_rw [e]
  have h := (((Real.hasDerivAt_cos 0).pow 2).mul_const A).add
    ((((Real.hasDerivAt_cos 0).mul (Real.hasDerivAt_sin 0)).mul_const B).add
      (((Real.hasDerivAt_sin 0).pow 2).mul_const C))
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply]; ring
  · simp

/-- A Lie curve is a real combination of the gate and of the gate times the generator. -/
theorem lieCurve_eq_comb {n : Type*} [Fintype n] [DecidableEq n] (U P : Matrix n n ℂ) (s : ℝ) :
    lieCurve U P s = (Real.cos s : ℂ) • U + (Real.sin s : ℂ) • (U * (Complex.I • P)) := by
  simp only [lieCurve, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [mul_comm Complex.I]

/-- The serial state is linear in each gate. -/
theorem gateState_perturb_linear (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (a b : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gateState L tbl (perturb G i (a • A + b • B)) x =
      a • gateState L tbl (perturb G i A) x + b • gateState L tbl (perturb G i B) x := by
  obtain ⟨φ, hφ⟩ := gate_split L tbl G i
  obtain ⟨Dn, hDn, -⟩ := hφ G (fun _ _ => rfl)
  rw [hDn, hDn, hDn]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem ip_eq_dotProduct (u v : Fin 2 → ℂ) : ip u v = star u ⬝ᵥ v := by
  simp [ip, dotProduct, Fin.sum_univ_two]

/-- Derivative of the serial output along a Lie coordinate curve. -/
theorem gateModel_lie_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    HasDerivAt (fun s => gateModel L tbl (perturb G i (lieCurve (G i) P s)) x)
      ((star (gateState L tbl G x) ⬝ᵥ (Zm *ᵥ gateState L tbl (perturb G i (G i * (Complex.I • P))) x)).re +
        (star (gateState L tbl (perturb G i (G i * (Complex.I • P))) x) ⬝ᵥ (Zm *ᵥ gateState L tbl G x)).re) 0 := by
  have e : ∀ s, gateModel L tbl (perturb G i (lieCurve (G i) P s)) x =
      (star ((Real.cos s : ℂ) • gateState L tbl G x +
        (Real.sin s : ℂ) • gateState L tbl (perturb G i (G i * (Complex.I • P))) x) ⬝ᵥ
      (Zm *ᵥ ((Real.cos s : ℂ) • gateState L tbl G x +
        (Real.sin s : ℂ) • gateState L tbl (perturb G i (G i * (Complex.I • P))) x))).re := by
    intro s
    unfold gateModel
    rw [lieCurve_eq_comb, gateState_perturb_linear, perturb_self, ip_eq_dotProduct]
  simp_rw [e]
  exact qform_curve_hasDerivAt Zm _ _

/-- The ancilla state is linear in each block. -/
theorem ancillaState_update_linear (x : ℝ) (a b : ℂ) (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (ℓ : Fin (L + 1)),
    ancillaState L (Function.update W ℓ (a • M + b • N)) x =
      a • ancillaState L (Function.update W ℓ M) x + b • ancillaState L (Function.update W ℓ N) x
  | 0, W, ℓ => by
    obtain rfl : ℓ = 0 := Fin.fin_one_eq_zero ℓ
    show (Function.update W 0 (a • M + b • N) 0) *ᵥ ket00 =
      a • (Function.update W 0 M 0 *ᵥ ket00) + b • (Function.update W 0 N 0 *ᵥ ket00)
    simp only [Function.update_self, Matrix.add_mulVec, Matrix.smul_mulVec]
  | L + 1, W, ℓ => by
    by_cases hℓ : ℓ = Fin.last (L + 1)
    · subst hℓ
      have hc : ∀ X, (fun i => Function.update W (Fin.last (L + 1)) X (Fin.castSucc i)) =
          fun i => W (Fin.castSucc i) := fun X => by
        funext i; exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
      show Function.update W _ (a • M + b • N) (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
        ancillaState L (fun i => Function.update W _ (a • M + b • N) (Fin.castSucc i)) x) =
        a • (Function.update W _ M (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
          ancillaState L (fun i => Function.update W _ M (Fin.castSucc i)) x)) +
        b • (Function.update W _ N (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
          ancillaState L (fun i => Function.update W _ N (Fin.castSucc i)) x))
      simp only [hc, Function.update_self, Matrix.add_mulVec, Matrix.smul_mulVec]
    · obtain ⟨ℓ', rfl⟩ := Fin.exists_castSucc_eq.mpr hℓ
      have hc : ∀ X, (fun i => Function.update W (Fin.castSucc ℓ') X (Fin.castSucc i)) =
          Function.update (fun i => W (Fin.castSucc i)) ℓ' X := fun X =>
        Function.update_comp_eq_of_injective W (Fin.castSucc_injective _) ℓ' X
      have ht : ∀ X, Function.update W (Fin.castSucc ℓ') X (Fin.last (L + 1)) = W (Fin.last (L + 1)) :=
        fun X => Function.update_of_ne (Fin.castSucc_lt_last ℓ').ne' _ _
      show Function.update W _ (a • M + b • N) (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
        ancillaState L (fun i => Function.update W _ (a • M + b • N) (Fin.castSucc i)) x) =
        a • (Function.update W _ M (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
          ancillaState L (fun i => Function.update W _ M (Fin.castSucc i)) x)) +
        b • (Function.update W _ N (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ
          ancillaState L (fun i => Function.update W _ N (Fin.castSucc i)) x))
      rw [ht, ht, ht, hc, hc, hc, ancillaState_update_linear x a b M N L]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- The ancilla state is linear in each gate. -/
theorem ancillaGateState_perturb_linear (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (i : Fin (L + 1) × Fin tbl) (a b : ℂ) (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    ancillaState L (fun ℓ => blockProd tbl (fun g => perturb G i (a • A + b • B) (ℓ, g))) x =
      a • ancillaState L (fun ℓ => blockProd tbl (fun g => perturb G i A (ℓ, g))) x +
        b • ancillaState L (fun ℓ => blockProd tbl (fun g => perturb G i B (ℓ, g))) x := by
  obtain ⟨U, D, -, -, hUD⟩ := gate_blocks_update G i
  rw [hUD, hUD, hUD]
  rw [show U * (a • A + b • B) * D = a • (U * A * D) + b • (U * B * D) by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]]
  exact ancillaState_update_linear x a b _ _ L _ _

/-- Derivative of the ancilla output along a Lie coordinate curve. -/
theorem ancillaGateModel_lie_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (i : Fin (L + 1) × Fin tbl) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    HasDerivAt (fun s => ancillaGateModel L tbl (perturb G i (lieCurve (G i) P s)) x)
      ((star (ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L
            (fun ℓ => blockProd tbl (fun g => perturb G i (G i * (Complex.I • P)) (ℓ, g))) x)).re +
        (star (ancillaState L (fun ℓ => blockProd tbl (fun g => perturb G i (G i * (Complex.I • P)) (ℓ, g))) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x)).re) 0 := by
  have e : ∀ s, ancillaGateModel L tbl (perturb G i (lieCurve (G i) P s)) x =
      (star ((Real.cos s : ℂ) • ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x +
        (Real.sin s : ℂ) • ancillaState L
          (fun ℓ => blockProd tbl (fun g => perturb G i (G i * (Complex.I • P)) (ℓ, g))) x) ⬝ᵥ
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
        ((Real.cos s : ℂ) • ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x +
        (Real.sin s : ℂ) • ancillaState L
          (fun ℓ => blockProd tbl (fun g => perturb G i (G i * (Complex.I • P)) (ℓ, g))) x))).re := by
    intro s
    unfold ancillaGateModel ancillaModel
    rw [lieCurve_eq_comb, ancillaGateState_perturb_linear, perturb_self]
  simp_rw [e]
  exact qform_curve_hasDerivAt _ _ _

/-- Entries of the serial coefficient Jacobian: the design inverse applied to the derivatives of the output at the
    grid points. -/
theorem gateJ_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (r : Fin (2 * L + 1)) (j : SIdx L tbl) :
    gateJ L tbl G r j = ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k *
      ((star (gateState L tbl G (eqGrid L 0 k)) ⬝ᵥ (Zm *ᵥ gateState L tbl (perturb G (j.1, j.2.1)
          (G (j.1, j.2.1) * (Complex.I • pauli j.2.2))) (eqGrid L 0 k))).re +
        (star (gateState L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauli j.2.2)))
          (eqGrid L 0 k)) ⬝ᵥ (Zm *ᵥ gateState L tbl G (eqGrid L 0 k))).re) := by
  set Gs : ℝ → Gates L tbl (Fin 2) :=
    fun s => perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s) with hGs
  have hrep : ∀ s, gateCoeffVec L tbl (Gs s) r =
      ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k * gateModel L tbl (Gs s) (eqGrid L 0 k) := by
    intro s
    conv_lhs => rw [vec_eq_design_inv L 0 (gateCoeffVec L tbl (Gs s))]
    simp only [Matrix.mulVec, dotProduct, gate_model_eq_design]
  have hd : HasDerivAt (fun s => gateCoeffVec L tbl (Gs s) r) (∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k *
      ((star (gateState L tbl G (eqGrid L 0 k)) ⬝ᵥ (Zm *ᵥ gateState L tbl (perturb G (j.1, j.2.1)
          (G (j.1, j.2.1) * (Complex.I • pauli j.2.2))) (eqGrid L 0 k))).re +
        (star (gateState L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauli j.2.2)))
          (eqGrid L 0 k)) ⬝ᵥ (Zm *ᵥ gateState L tbl G (eqGrid L 0 k))).re)) 0 := by
    simp_rw [hrep]
    exact HasDerivAt.fun_sum fun k _ =>
      (gateModel_lie_hasDerivAt L tbl G (j.1, j.2.1) (pauli j.2.2) (eqGrid L 0 k)).const_mul _
  exact (gateCoeffVec_hasDerivAt L tbl G j r).unique hd

/-- Entries of the ancilla coefficient Jacobian. -/
theorem ancillaJ_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (r : Fin (2 * L + 1)) (j : AIdx L tbl) :
    ancillaJ L tbl G r j = ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k *
      ((star (ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) (eqGrid L 0 k)) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L
            (fun ℓ => blockProd tbl (fun g => perturb G (j.1, j.2.1)
              (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)) (ℓ, g))) (eqGrid L 0 k))).re +
        (star (ancillaState L (fun ℓ => blockProd tbl (fun g => perturb G (j.1, j.2.1)
              (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)) (ℓ, g))) (eqGrid L 0 k)) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            ancillaState L (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) (eqGrid L 0 k))).re) := by
  set Gs : ℝ → Gates L tbl (Fin 2 × Fin 2) :=
    fun s => perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s) with hGs
  have hrep : ∀ s, ancillaCoeffVec L tbl (Gs s) r =
      ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k * ancillaGateModel L tbl (Gs s) (eqGrid L 0 k) := by
    intro s
    conv_lhs => rw [vec_eq_design_inv L 0 (ancillaCoeffVec L tbl (Gs s))]
    simp only [Matrix.mulVec, dotProduct, ancilla_model_eq_design]
  refine (ancillaCoeffVec_hasDerivAt L tbl G j r).unique ?_
  show HasDerivAt (fun s => ancillaCoeffVec L tbl (Gs s) r) _ 0
  simp_rw [hrep]
  exact HasDerivAt.fun_sum fun k _ =>
    (ancillaGateModel_lie_hasDerivAt L tbl G (j.1, j.2.1) (pauliWord j.2.2) (eqGrid L 0 k)).const_mul _

end

end


/-! # Auxiliary results for the full-rank witnesses of Lemma 3.3(ii) -/

@[expose] public section

open Matrix

set_option autoImplicit false

noncomputable section

/-- Derivative of the serial output when gate `i` moves along any differentiable curve. -/
theorem gateModel_curve_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (A' : Matrix (Fin 2) (Fin 2) ℂ) (hγ0 : γ 0 = G i)
    (hγ : ∀ a b, HasDerivAt (fun s => γ s a b) (A' a b) 0) (x : ℝ) :
    HasDerivAt (fun s => gateModel L tbl (perturb G i (γ s)) x)
      (2 * (ip (gateState L tbl (perturb G i A') x) (Zm *ᵥ gateState L tbl G x)).re) 0 := by
  obtain ⟨φ, hφ⟩ := gate_split L tbl G i
  obtain ⟨Dn, hDn, -⟩ := hφ G (fun _ _ => rfl)
  have hst : HasDerivAt (fun s => gateState L tbl (perturb G i (γ s)) x)
      (gateState L tbl (perturb G i A') x) 0 := by
    simp only [hDn]
    have h1 := hasDerivAt_mulVec_curve γ A' (fun _ => φ x) 0 hγ (hasDerivAt_const _ _)
    simp only [Matrix.mulVec_zero, add_zero] at h1
    exact hasDerivAt_mulVec (Dn x) _ _ 0 h1
  have h := expval_hasDerivAt Zm Zm_hermitian _ _ 0 hst
  rw [hγ0, perturb_self] at h
  exact h

/-- Grid-sampled column associated with moving gate `i` with velocity `A`. -/
def gcol (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Fin (2 * L + 1) → ℝ := fun r => ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k *
  (2 * (ip (gateState L tbl (perturb G i A) (eqGrid L 0 k)) (Zm *ᵥ gateState L tbl G (eqGrid L 0 k))).re)

theorem ip_add_left' (u v w : Fin 2 → ℂ) : ip (u + v) w = ip u w + ip v w := by
  simp only [ip, Pi.add_apply, map_add]; ring

theorem ip_smul_left' (a : ℂ) (u w : Fin 2 → ℂ) : ip (a • u) w = (starRingEnd ℂ) a * ip u w := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem gcol_add (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : gcol L tbl G i (A + B) = gcol L tbl G i A + gcol L tbl G i B := by
  funext r
  have hl : ∀ x, gateState L tbl (perturb G i (A + B)) x =
      gateState L tbl (perturb G i A) x + gateState L tbl (perturb G i B) x := by
    intro x
    have := gateState_perturb_linear L tbl G i 1 1 A B x
    simpa using this
  simp only [gcol, Pi.add_apply, hl, ip_add_left', Complex.add_re, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem gcol_smul (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : gcol L tbl G i ((c : ℂ) • A) = c • gcol L tbl G i A := by
  funext r
  have hl : ∀ x, gateState L tbl (perturb G i ((c : ℂ) • A)) x =
      (c : ℂ) • gateState L tbl (perturb G i A) x := by
    intro x
    have := gateState_perturb_linear L tbl G i (c : ℂ) 0 A 0 x
    simpa using this
  simp only [gcol, Pi.smul_apply, hl, ip_smul_left', Complex.conj_ofReal, Complex.re_ofReal_mul,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A multiple of `i · 1` does not move the output. -/
theorem gcol_I (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl) :
    gcol L tbl G i (G i * (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 0 := by
  funext r
  have hl : ∀ x, gateState L tbl (perturb G i (G i * (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)))) x =
      Complex.I • gateState L tbl G x := by
    intro x
    have := gateState_perturb_linear L tbl G i Complex.I 0 (G i) 0 x
    simpa [perturb_self, Matrix.mul_smul] using this
  simp only [gcol, hl, ip_smul_left', Complex.conj_I, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  have him := ip_herm_im Zm_hermitian (gateState L tbl G (eqGrid L 0 k))
  simp [Complex.mul_re, him]

theorem qform_Zm_sum (u v : Fin 2 → ℂ) :
    (star u ⬝ᵥ (Zm *ᵥ v)).re + (star v ⬝ᵥ (Zm *ᵥ u)).re = 2 * (ip v (Zm *ᵥ u)).re := by
  rw [← ip_eq_dotProduct, ← ip_eq_dotProduct, ip_herm_swap Zm_hermitian u v, Complex.conj_re]
  ring

/-- Columns of the serial coefficient Jacobian are grid-sampled columns. -/
theorem gateJ_col (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (r : Fin (2 * L + 1)) (j : SIdx L tbl) :
    gateJ L tbl G r j = gcol L tbl G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauli j.2.2)) r := by
  rw [gateJ_eq, gcol]
  exact Finset.sum_congr rfl fun k _ => by rw [qform_Zm_sum]

/-- Every anti-Hermitian `2 × 2` matrix is `i (h₀ 1 + Σ_a r_a σ_a)` with real coefficients. -/
theorem antiHerm_decomp (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = -X) :
    ∃ (h0 : ℝ) (rr : Fin 3 → ℝ), X = ((h0 : ℂ) • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) +
      ∑ a, ((rr a : ℂ) • (Complex.I • pauli a)) := by
  have e : ∀ a b, (starRingEnd ℂ) (X b a) = -X a b := fun a b => by
    have := congrFun (congrFun hX a) b
    simpa [conjTranspose_apply] using this
  have e00 := e 0 0
  have e11 := e 1 1
  have e01 := e 0 1
  rw [Complex.ext_iff] at e00 e11 e01
  simp at e00 e11 e01
  refine ⟨((X 0 0).im + (X 1 1).im) / 2, ![(X 0 1).im, (X 0 1).re, ((X 0 0).im - (X 1 1).im) / 2], ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, pauli, pauli1, Complex.ext_iff] <;>
    constructor <;> linarith

/-- A velocity `A' = G_i X` with `X` anti-Hermitian gives a column in the span of the Lie-coordinate columns. -/
theorem gcol_mem_range (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (i : Fin (L + 1) × Fin tbl)
    (hGi : G i ∈ Matrix.unitaryGroup (Fin 2) ℂ) (A' : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : (star (G i) * A')ᴴ = -(star (G i) * A')) :
    gcol L tbl G i A' ∈ LinearMap.range (gateJ L tbl G).mulVecLin := by
  obtain ⟨h0, rr, hdec⟩ := antiHerm_decomp _ hX
  have hA : A' = G i * (star (G i) * A') := by
    rw [← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff).1 hGi, Matrix.one_mul]
  have hA2 : A' = (h0 : ℂ) • (G i * (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) +
      ((rr 0 : ℂ) • (G i * (Complex.I • pauli 0)) + ((rr 1 : ℂ) • (G i * (Complex.I • pauli 1)) +
        (rr 2 : ℂ) • (G i * (Complex.I • pauli 2)))) := by
    conv_lhs => rw [hA, hdec]
    simp only [Fin.sum_univ_three, Matrix.mul_add, Matrix.mul_smul, add_assoc]
  refine ⟨∑ a : Fin 3, rr a • (Pi.single (i.1, i.2, a) (1 : ℝ) : SIdx L tbl → ℝ), ?_⟩
  rw [hA2, gcol_add, gcol_add, gcol_add, gcol_smul, gcol_smul, gcol_smul, gcol_smul, gcol_I]
  funext r
  simp only [Matrix.mulVecLin_apply, Fin.sum_univ_three, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, Matrix.col_apply, Pi.zero_apply,
    gateJ_col, smul_eq_mul]
  ring

/-- The velocity of a curve of unitaries is `γ(0) X` with `X` anti-Hermitian. -/
theorem velocity_antiHerm (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (A' : Matrix (Fin 2) (Fin 2) ℂ)
    (hγ : ∀ a b, HasDerivAt (fun s => γ s a b) (A' a b) 0) (hU : ∀ s, γ s ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (star (γ 0) * A')ᴴ = -(star (γ 0) * A') := by
  have h : ∀ a b, HasDerivAt (fun s => (star (γ s) * γ s) a b) ((star A' * γ 0 + star (γ 0) * A') a b) 0 := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun c _ => by
      have := ((hγ c a).star).mul (hγ c b)
      convert this using 1
  have h0 : ∀ a b, (star A' * γ 0 + star (γ 0) * A') a b = 0 := by
    intro a b
    have hc : (fun s => (star (γ s) * γ s) a b) = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) a b :=
      funext fun s => by rw [(Matrix.mem_unitaryGroup_iff').1 (hU s)]
    have h' := h a b
    rw [hc] at h'
    exact h'.unique (hasDerivAt_const _ _)
  have h1 : star A' * γ 0 = -(star (γ 0) * A') := by
    rw [eq_neg_iff_add_eq_zero]
    ext a b
    exact h0 a b
  rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star]
  exact h1

/-- Gates given by Euler angles. -/
def rotGates (L tbl : ℕ) (θ : Params L tbl) : Gates L tbl (Fin 2) :=
  fun i => Rot (θ i.1 i.2 0) (θ i.1 i.2 1) (θ i.1 i.2 2)

theorem blockProd_rot_eq_stackRot : ∀ (tbl : ℕ) (Θ : Fin tbl → Fin 3 → ℝ),
    blockProd tbl (fun t => Rot (Θ t 0) (Θ t 1) (Θ t 2)) = stackRot tbl Θ
  | 0, _ => rfl
  | t + 1, Θ => by
    rw [blockProd, stackRot, ← blockProd_rot_eq_stackRot t]

theorem gateModel_rotGates (L tbl : ℕ) (θ : Params L tbl) (x : ℝ) :
    gateModel L tbl (rotGates L tbl θ) x = model L tbl θ x := by
  unfold gateModel model gateState circuitState
  simp only [rotGates, blockProd_rot_eq_stackRot]

theorem rotGates_InSU (L tbl : ℕ) (θ : Params L tbl) : InSU (rotGates L tbl θ) :=
  fun _ => rot_mem_SU2 _ _ _

theorem rotGates_dirVec (L tbl : ℕ) (θ : Params L tbl) (j : Idx L tbl) (s : ℝ) :
    rotGates L tbl (θ + s • dirVec j) =
      perturb (rotGates L tbl θ) (j.1, j.2.1) (rotGates L tbl (θ + s • dirVec j) (j.1, j.2.1)) := by
  funext i
  by_cases hi : i = (j.1, j.2.1)
  · subst hi; simp [perturb]
  · rw [perturb, Function.update_of_ne hi]
    have hz : ∀ c, dirVec j i.1 i.2 c = 0 := by
      intro c
      simp only [dirVec]
      rw [if_neg]
      intro h
      apply hi
      rw [← h]
    simp [rotGates, hz]

/-- The Euler-angle curve of one gate has an entrywise derivative at `0`. -/
theorem rotGates_curve_hasDerivAt (L tbl : ℕ) (θ : Params L tbl) (j : Idx L tbl) (a b : Fin 2) :
    HasDerivAt (fun s : ℝ => rotGates L tbl (θ + s • dirVec j) (j.1, j.2.1) a b)
      (deriv (fun s : ℝ => rotGates L tbl (θ + s • dirVec j) (j.1, j.2.1) a b) 0) 0 := by
  have hc : ∀ c, AnalyticAt ℝ (fun s : ℝ => (θ + s • dirVec j) j.1 j.2.1 c) 0 := by
    intro c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have := (analyticAt_Rot_entry (hc 0) (hc 1) (hc 2) a b).differentiableAt.hasDerivAt
  simpa only [rotGates] using this

/-- Entries of the design matrix are bounded by `2`. -/
theorem abs_designEntry_le (L : ℕ) (x : ℝ) (r : Fin (2 * L + 1)) : |designEntry L x r| ≤ 2 := by
  unfold designEntry designMatrix
  split_ifs
  · norm_num
  · rw [abs_mul]; have := Real.abs_cos_le_one ((((r : ℕ) + 1) / 2 : ℕ) * x); norm_num; linarith
  · rw [abs_mul]; have := Real.abs_sin_le_one (((r : ℕ) / 2 : ℕ) * x); norm_num; linarith

/-- Small coefficient vectors are coefficient vectors of serial circuits. -/
theorem small_coeff_realised (hFR : FejerRieszHyp) (hQ : GQSPHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (v : Fin (2 * L + 1) → ℝ) (hv : ‖v‖ < 1 / (2 * (2 * (L : ℝ) + 1))) :
    ∃ θ : Params L tbl, gateCoeffVec L tbl (rotGates L tbl θ) = v := by
  set g : ℝ → ℝ := fun x => ∑ r, designEntry L x r * v r with hg
  have hvr : ∀ r, |v r| ≤ 1 / (2 * (2 * (L : ℝ) + 1)) := fun r =>
    ((norm_le_pi_norm v r).trans hv.le)
  have hgb : ∀ x, |g x| ≤ 1 := by
    intro x
    calc |g x| ≤ ∑ r, |designEntry L x r * v r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin (2 * L + 1), 2 * (1 / (2 * (2 * (L : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_designEntry_le L x r) (hvr r) (abs_nonneg _) (by norm_num)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
  have hgFE : g ∈ FE L := ⟨unRealRep L v, unRealRep_supp L v, fun x => design_eq_trig L v x, hgb⟩
  rw [← serial_class_eq hFR hQ L tbl htbl] at hgFE
  obtain ⟨G, hG, hGg⟩ := hgFE
  choose φ θ' ω hrot using fun i => rot_surjective (G i) (hG i)
  refine ⟨fun ℓ t => ![φ (ℓ, t), θ' (ℓ, t), ω (ℓ, t)], ?_⟩
  have hRG : rotGates L tbl (fun ℓ t => ![φ (ℓ, t), θ' (ℓ, t), ω (ℓ, t)]) = G := by
    funext i
    simpa [rotGates] using hrot i
  rw [hRG, gateCoeffVec, ← hGg, hg, realRep_realFourierCoeff_design]

/-- A Lie curve of `P ⊗ 1` through `S (U ⊗ 1)` is `S` times the Lie curve of `P` through `U`, tensored with `1`. -/
theorem lieCurve_kron (S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (U P : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    lieCurve (S * Matrix.kronecker U 1) (Matrix.kronecker P 1) s =
      S * Matrix.kronecker (lieCurve U P s) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [lieCurve_eq_comb, lieCurve_eq_comb]
  unfold Matrix.kronecker
  have hk : kroneckerMap (· * ·) (U * (Complex.I • P)) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      kroneckerMap (· * ·) U (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (Complex.I • kroneckerMap (· * ·) P (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [← Matrix.smul_kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker, hk, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_assoc]
  simp only [Matrix.mul_smul]

theorem ancillaEmbed_update_lie (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : Fin (L + 1))
    (P : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    ancillaEmbed L (Function.update V ℓ (lieCurve (V ℓ) P s)) =
      Function.update (ancillaEmbed L V) ℓ (lieCurve (ancillaEmbed L V ℓ) (Matrix.kronecker P 1) s) := by
  funext ℓ'
  by_cases h : ℓ' = ℓ
  · subst h
    rw [Function.update_self]
    unfold ancillaEmbed
    split_ifs
    · rw [Function.update_self, lieCurve_kron]
    · rw [Function.update_self]
      have := lieCurve_kron 1 (V ℓ') P s
      rw [Matrix.one_mul, Matrix.one_mul] at this
      exact this.symm
  · rw [Function.update_of_ne h]
    unfold ancillaEmbed
    rw [Function.update_of_ne h]

/-- The ancilla output of embedded gates along a `P ⊗ 1` Lie curve is the serial output along the `P` curve. -/
theorem ancilla_embed_lie_model (L tbl : ℕ) (htbl : 1 ≤ tbl) (Gs : Gates L 1 (Fin 2)) (ℓ : Fin (L + 1))
    (a : Fin 3) (s x : ℝ) :
    ancillaGateModel L tbl (perturb (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0)))) (ℓ, ⟨0, htbl⟩)
      (lieCurve (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0))) (ℓ, ⟨0, htbl⟩))
        (Matrix.kronecker (pauli a) 1) s)) x =
      gateModel L 1 (perturb Gs (ℓ, 0) (lieCurve (Gs (ℓ, 0)) (pauli a) s)) x := by
  set V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ := fun ℓ => Gs (ℓ, 0) with hV
  set V' := Function.update V ℓ (lieCurve (V ℓ) (pauli a) s) with hV'
  have hga : perturb (singleGates L tbl (ancillaEmbed L V)) (ℓ, ⟨0, htbl⟩)
      (lieCurve (singleGates L tbl (ancillaEmbed L V) (ℓ, ⟨0, htbl⟩)) (Matrix.kronecker (pauli a) 1) s) =
      singleGates L tbl (ancillaEmbed L V') := by
    rw [hV', ancillaEmbed_update_lie]
    funext i
    obtain ⟨ℓ', t'⟩ := i
    by_cases h : (ℓ', t') = (ℓ, ⟨0, htbl⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp [perturb, singleGates]
    · rw [perturb, Function.update_of_ne h]
      unfold singleGates
      split_ifs with ht
      · have hℓ : ℓ' ≠ ℓ := by
          intro hl; apply h; rw [hl]; congr 1; exact Fin.ext ht
        rw [Function.update_of_ne hℓ]
      · rfl
  have hgs : (fun ℓ' => blockProd 1 (fun g => perturb Gs (ℓ, 0) (lieCurve (Gs (ℓ, 0)) (pauli a) s) (ℓ', g))) =
      V' := by
    funext ℓ'
    simp only [blockProd, Matrix.mul_one]
    by_cases h : ℓ' = ℓ
    · subst h; simp [perturb, hV', hV]
    · rw [hV', Function.update_of_ne h, perturb, Function.update_of_ne]
      · rfl
      · intro h'; exact h (congrArg Prod.fst h')
  unfold ancillaGateModel
  rw [hga, show (fun ℓ => blockProd tbl (fun g => singleGates L tbl (ancillaEmbed L V') (ℓ, g))) =
    ancillaEmbed L V' from funext fun ℓ => singleGates_blockProd L tbl htbl _ ℓ, ancillaModel_embed]
  unfold gateModel gateState
  rw [hgs]

/-- The two-qubit Pauli word `σ_a ⊗ I`. -/
def ancWord (a : Fin 3) : PWord := ⟨(a.succ, 0), by simp [Fin.succ_ne_zero]⟩

theorem pauliWord_ancWord (a : Fin 3) : pauliWord (ancWord a) = Matrix.kronecker (pauli a) 1 := by
  simp [ancWord, pauliWord, pauli, pauli1]

/-- Serial Lie coordinates as ancilla Lie coordinates of the embedded circuit. -/
def ancIdx (L tbl : ℕ) (htbl : 1 ≤ tbl) (j : SIdx L 1) : AIdx L tbl := (j.1, ⟨0, htbl⟩, ancWord j.2.2)

theorem ancillaJ_embed_col (L tbl : ℕ) (htbl : 1 ≤ tbl) (Gs : Gates L 1 (Fin 2)) (r : Fin (2 * L + 1))
    (j : SIdx L 1) :
    ancillaJ L tbl (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0)))) r (ancIdx L tbl htbl j) =
      gateJ L 1 Gs r j := by
  obtain ⟨ℓ, t, a⟩ := j
  obtain rfl : t = 0 := Subsingleton.elim _ _
  unfold ancillaJ gateJ
  have h : ∀ s, ancillaCoeffVec L tbl (perturb (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0))))
      (ℓ, ⟨0, htbl⟩) (lieCurve (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0))) (ℓ, ⟨0, htbl⟩))
        (pauliWord (ancWord a)) s)) r =
      gateCoeffVec L 1 (perturb Gs (ℓ, 0) (lieCurve (Gs (ℓ, 0)) (pauli a) s)) r := by
    intro s
    unfold ancillaCoeffVec gateCoeffVec
    rw [pauliWord_ancWord]
    congr 2
    funext x
    exact ancilla_embed_lie_model L tbl htbl Gs ℓ a s x
  exact congrArg (fun F => deriv F 0) (funext h)

end

end


/-! # Section 19: Lemma B.1 and Lemma 3.3(ii) -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 19. Lemma B.1 and Lemma 3.3(ii): full row rank for almost every choice of gates -/

/-- A square real matrix of full rank has nonzero determinant. -/
theorem det_ne_zero_of_rank_eq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (h : A.rank = m) : A.det ≠ 0 := by
  have hker := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [← Matrix.rank, h, Module.finrank_fin_fun] at hker
  have h0 : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by omega
  have hbot := Submodule.finrank_eq_zero.mp h0
  have hinj : Function.Injective A.mulVec := by
    intro v w hvw
    have : v - w ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hvw, sub_self]
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hu := (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  exact ((Matrix.isUnit_iff_isUnit_det A).mp hu).ne_zero

/-- Full row rank is equivalent to a nonzero Gram determinant. -/
theorem gram_det_ne_zero_iff {m : ℕ} {κ : Type*} [Fintype κ] (J : Matrix (Fin m) κ ℝ) :
    (J * Jᵀ).det ≠ 0 ↔ J.rank = m := by
  constructor
  · intro h
    have hu : IsUnit (J * Jᵀ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
    have := Matrix.rank_of_isUnit _ hu
    rw [Matrix.rank_self_mul_transpose, Fintype.card_fin] at this
    exact this
  · intro h
    apply det_ne_zero_of_rank_eq
    rw [Matrix.rank_self_mul_transpose, h]

/-- **Lemma B.1.** If `det(JJᵀ)` is a polynomial in the real and imaginary parts of the gate entries on SU(d)^m and
    `J` has full row rank at one point of SU(d)^m, it has full row rank outside a `μ`-null set, for every `μ` with the
    cited null-set property (Haar measure). -/
theorem genericity {ι n κ : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Fintype κ] {m : ℕ}
    (Jmap : (ι → Matrix n n ℂ) → Matrix (Fin m) κ ℝ)
    (hpoly : ∃ q : MvPolynomial (ι × n × n × Bool) ℝ, ∀ G : ι → Matrix n n ℂ,
      (∀ i, G i ∈ Matrix.specialUnitaryGroup n ℂ) → MvPolynomial.eval (reIm G) q = (Jmap G * (Jmap G)ᵀ).det)
    (G₀ : ι → Matrix n n ℂ) (hG₀ : ∀ i, G₀ i ∈ Matrix.specialUnitaryGroup n ℂ) (hrank : (Jmap G₀).rank = m)
    (μ : MeasureTheory.Measure (ι → n → n → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup n ℂ) ∧
      (Jmap (fun i => Matrix.of (G i))).rank < m} = 0 := by
  obtain ⟨q, hq⟩ := hpoly
  have hne : MvPolynomial.eval (reIm G₀) q ≠ 0 := by
    rw [hq G₀ hG₀]
    exact (gram_det_ne_zero_iff _).2 hrank
  refine measure_mono_null ?_ (hμ q ⟨G₀, hG₀, hne⟩)
  rintro G ⟨hSU, hlt⟩
  refine ⟨hSU, ?_⟩
  rw [hq _ hSU]
  by_contra h
  exact (ne_of_lt hlt) ((gram_det_ne_zero_iff _).1 h)

theorem serial_gramDet_poly (L tbl : ℕ) :
    ∃ q : MvPolynomial ((Fin (L + 1) × Fin tbl) × Fin 2 × Fin 2 × Bool) ℝ, ∀ G : Gates L tbl (Fin 2),
      InSU G → MvPolynomial.eval (reIm G) q = (gateJ L tbl G * (gateJ L tbl G)ᵀ).det := by
  have hblk : ∀ (F : Gates L tbl (Fin 2) → Gates L tbl (Fin 2)),
      (∀ i a b, IsCPoly (fun G => F G i a b)) → ∀ x a,
      IsCPoly (fun G => gateState L tbl (F G) x a) := by
    intro F hF x a
    exact IsCPoly.serialState x L (fun G ℓ => blockProd tbl (fun g => F G (ℓ, g)))
      (fun ℓ => IsCPoly.blockProd tbl (fun G g => F G (ℓ, g)) (fun g => hF _)) a
  have hJ : ∀ r j, IsRPoly (fun G => gateJ L tbl G r j) := by
    intro r j
    refine (IsRPoly.sum Finset.univ fun k _ => (IsRPoly.const _).mul
      ((IsRPoly.qform Zm (hblk id (fun i a b => IsCPoly.entry i a b) _)
        (hblk _ (IsCPoly.perturb_mul _ _) _)).add
      (IsRPoly.qform Zm (hblk _ (IsCPoly.perturb_mul _ _) _)
        (hblk id (fun i a b => IsCPoly.entry i a b) _)))).congr fun G => (gateJ_eq L tbl G r j).symm
  obtain ⟨q, hq⟩ := IsRPoly.det (fun G => gateJ L tbl G * (gateJ L tbl G)ᵀ) (fun a b =>
    (IsRPoly.sum Finset.univ fun j _ => (hJ a j).mul (hJ b j)).congr fun G => by
      simp [Matrix.mul_apply])
  exact ⟨q, fun G _ => (hq G).symm⟩

theorem ancilla_gramDet_poly (L tbl : ℕ) :
    ∃ q : MvPolynomial ((Fin (L + 1) × Fin tbl) × (Fin 2 × Fin 2) × (Fin 2 × Fin 2) × Bool) ℝ,
      ∀ G : Gates L tbl (Fin 2 × Fin 2),
      InSU G → MvPolynomial.eval (reIm G) q = (ancillaJ L tbl G * (ancillaJ L tbl G)ᵀ).det := by
  have hblk : ∀ (F : Gates L tbl (Fin 2 × Fin 2) → Gates L tbl (Fin 2 × Fin 2)),
      (∀ i a b, IsCPoly (fun G => F G i a b)) → ∀ x a,
      IsCPoly (fun G => ancillaState L (fun ℓ => blockProd tbl (fun g => F G (ℓ, g))) x a) := by
    intro F hF x a
    exact IsCPoly.ancillaState x L (fun G ℓ => blockProd tbl (fun g => F G (ℓ, g)))
      (fun ℓ => IsCPoly.blockProd tbl (fun G g => F G (ℓ, g)) (fun g => hF _)) a
  have hJ : ∀ r j, IsRPoly (fun G => ancillaJ L tbl G r j) := by
    intro r j
    refine (IsRPoly.sum Finset.univ fun k _ => (IsRPoly.const _).mul
      ((IsRPoly.qform (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm) (hblk id (fun i a b => IsCPoly.entry i a b) _)
        (hblk _ (IsCPoly.perturb_mul _ _) _)).add
      (IsRPoly.qform (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm) (hblk _ (IsCPoly.perturb_mul _ _) _)
        (hblk id (fun i a b => IsCPoly.entry i a b) _)))).congr fun G => (ancillaJ_eq L tbl G r j).symm
  obtain ⟨q, hq⟩ := IsRPoly.det (fun G => ancillaJ L tbl G * (ancillaJ L tbl G)ᵀ) (fun a b =>
    (IsRPoly.sum Finset.univ fun j _ => (hJ a j).mul (hJ b j)).congr fun G => by
      simp [Matrix.mul_apply])
  exact ⟨q, fun G _ => (hq G).symm⟩

/-- A full-rank point of the serial circuit (Sard + Lemma 3.3(i)). -/
theorem serial_full_rank_witness (hFR : FejerRieszHyp) (hQ : GQSPHyp) (hS : SardHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    ∃ G : Gates L tbl (Fin 2), InSU G ∧ (gateJ L tbl G).rank = 2 * L + 1 := by
  classical
  set N := Fintype.card (Idx L tbl) with hN
  set idx := Fintype.equivFin (Idx L tbl) with hidx
  let eθ : (Fin N → ℝ) →L[ℝ] Params L tbl :=
    ContinuousLinearMap.pi fun ℓ => ContinuousLinearMap.pi fun t => ContinuousLinearMap.pi fun c =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) (idx (ℓ, t, c))
  have heθ : ∀ y ℓ t c, eθ y ℓ t c = y (idx (ℓ, t, c)) := fun _ _ _ _ => rfl
  set Binv := (designMatrix L (eqGrid L 0))⁻¹ with hBinv
  let F : (Fin N → ℝ) → (Fin (2 * L + 1) → ℝ) := fun y r =>
    ∑ k, Binv r k * model L tbl (eθ y) (eqGrid L 0 k)
  have hFc : ∀ k : ℕ, ContDiff ℝ k F := by
    intro k
    rw [contDiff_pi]
    intro r
    exact ContDiff.sum fun m _ => contDiff_const.mul (((model_analytic L tbl _).contDiff).comp eθ.contDiff)
  have hsard := hS N (2 * L + 1) F hFc
  have hFG : ∀ y, F y = gateCoeffVec L tbl (rotGates L tbl (eθ y)) := by
    intro y
    conv_rhs => rw [vec_eq_design_inv L 0 (gateCoeffVec L tbl (rotGates L tbl (eθ y)))]
    funext r
    simp only [F, Matrix.mulVec, dotProduct, ← gate_model_eq_design, gateModel_rotGates, Binv]
  have hball : Metric.ball (0 : Fin (2 * L + 1) → ℝ) (1 / (2 * (2 * (L : ℝ) + 1))) ⊆ Set.range F := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    obtain ⟨θ, hθ⟩ := small_coeff_realised hFR hQ L tbl htbl v hv
    refine ⟨fun p => θ (idx.symm p).1 (idx.symm p).2.1 (idx.symm p).2.2, ?_⟩
    rw [hFG]
    have : eθ (fun p => θ (idx.symm p).1 (idx.symm p).2.1 (idx.symm p).2.2) = θ := by
      funext ℓ t c; simp [heθ]
    rw [this, hθ]
  obtain ⟨y, hy⟩ : ∃ y, LinearMap.range (fderiv ℝ F y : (Fin N → ℝ) →ₗ[ℝ] (Fin (2 * L + 1) → ℝ)) = ⊤ := by
    by_contra hcon
    push_neg at hcon
    have hsub : Metric.ball (0 : Fin (2 * L + 1) → ℝ) (1 / (2 * (2 * (L : ℝ) + 1))) ⊆
        F '' {θ | LinearMap.range (fderiv ℝ F θ : (Fin N → ℝ) →ₗ[ℝ] (Fin (2 * L + 1) → ℝ)) ≠ ⊤} := by
      intro v hv
      obtain ⟨y, rfl⟩ := hball hv
      exact ⟨y, hcon y, rfl⟩
    have hpos := Metric.measure_ball_pos MeasureTheory.volume (0 : Fin (2 * L + 1) → ℝ)
      (by positivity : (0 : ℝ) < 1 / (2 * (2 * (L : ℝ) + 1)))
    exact absurd (MeasureTheory.measure_mono_null hsub hsard) hpos.ne'
  set θ := eθ y with hθ
  set G := rotGates L tbl θ with hG
  refine ⟨G, rotGates_InSU L tbl θ, ?_⟩
  have hdiffF : DifferentiableAt ℝ F y := ((hFc 1).differentiable (by norm_num)) y
  have hcol : ∀ p : Fin N, fderiv ℝ F y (Pi.single p 1) ∈ LinearMap.range (gateJ L tbl G).mulVecLin := by
    intro p
    set ep : Fin N → ℝ := Pi.single p (1 : ℝ) with hep
    set j := idx.symm p with hj
    set γ := fun s : ℝ => rotGates L tbl (θ + s • dirVec j) (j.1, j.2.1) with hγdef
    set A' : Matrix (Fin 2) (Fin 2) ℂ := fun a b => deriv (fun s => γ s a b) 0 with hA'
    have hγ : ∀ a b, HasDerivAt (fun s => γ s a b) (A' a b) 0 := rotGates_curve_hasDerivAt L tbl θ j
    have hγ0 : γ 0 = G (j.1, j.2.1) := by simp [hγdef, hG]
    have hline : ∀ s : ℝ, eθ (y + s • ep) = θ + s • dirVec j := by
      intro s
      rw [map_add, map_smul]
      funext ℓ t c
      simp only [Pi.add_apply, Pi.smul_apply, heθ, dirVec, hθ]
      congr 2
      by_cases h : (ℓ, t, c) = j
      · rw [if_pos h, hep, Pi.single_apply, if_pos]
        rw [h]
        exact Equiv.apply_symm_apply idx p
      · rw [if_neg h, hep, Pi.single_apply, if_neg]
        intro h'
        apply h
        rw [hj, ← h', Equiv.symm_apply_apply]
    have h1 : HasDerivAt (fun s : ℝ => F (y + s • ep)) (fderiv ℝ F y (ep)) 0 := by
      have hl : HasDerivAt (fun s : ℝ => y + s • ep) (ep) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ep)).const_add y
      have hF' : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • ep) := by
        simpa using hdiffF.hasFDerivAt
      exact hF'.comp_hasDerivAt (0 : ℝ) hl
    have h2 : HasDerivAt (fun s : ℝ => F (y + s • ep)) (gcol L tbl G (j.1, j.2.1) A') 0 := by
      rw [hasDerivAt_pi]
      intro r
      have e : (fun s : ℝ => F (y + s • ep) r) = fun s =>
          ∑ k, Binv r k * gateModel L tbl (perturb G (j.1, j.2.1) (γ s)) (eqGrid L 0 k) := by
        funext s
        simp only [F]
        rw [hline]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← gateModel_rotGates, rotGates_dirVec]
      rw [e]
      exact HasDerivAt.fun_sum fun k _ =>
        (gateModel_curve_hasDerivAt L tbl G _ γ A' hγ0 hγ _).const_mul _
    rw [h1.unique h2]
    apply gcol_mem_range L tbl G _ (rot_mem_SU2 _ _ _).1 A'
    rw [← hγ0]
    exact velocity_antiHerm γ A' hγ (fun s => (rot_mem_SU2 _ _ _).1)
  have htop : LinearMap.range (gateJ L tbl G).mulVecLin = ⊤ := by
    rw [eq_top_iff, ← hy, LinearMap.range_eq_map, ← (Pi.basisFun ℝ (Fin N)).span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    simpa [Pi.basisFun_apply] using hcol p
  rw [Matrix.rank, htop, finrank_top, Module.finrank_fin_fun]

/-- A full-rank point of the ancilla circuit: the embedded serial witness. -/
theorem ancilla_full_rank_witness (hFR : FejerRieszHyp) (hQ : GQSPHyp) (hS : SardHyp) (L tbl : ℕ)
    (htbl : 1 ≤ tbl) :
    ∃ G : Gates L tbl (Fin 2 × Fin 2), InSU G ∧ (ancillaJ L tbl G).rank = 2 * L + 1 := by
  obtain ⟨Gs, hGs, hrank⟩ := serial_full_rank_witness hFR hQ hS L 1 le_rfl
  refine ⟨singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0))),
    singleGates_InSU _ _ _ (ancillaEmbed_mem_SU4 L _ (fun ℓ => hGs _)), ?_⟩
  have hsub : (ancillaJ L tbl (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0)))))ᵀ.submatrix
      (ancIdx L tbl htbl) (Equiv.refl _) = (gateJ L 1 Gs)ᵀ := by
    ext j r
    exact ancillaJ_embed_col L tbl htbl Gs r j
  have h1 : (ancillaJ L tbl (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0))))).rank ≤ 2 * L + 1 :=
    (Matrix.rank_le_card_height _).trans (by simp)
  have h2 : (gateJ L 1 Gs)ᵀ.rank ≤
      (ancillaJ L tbl (singleGates L tbl (ancillaEmbed L (fun ℓ => Gs (ℓ, 0)))))ᵀ.rank := by
    rw [← hsub]
    exact Matrix.rank_submatrix_le _ _ _
  rw [Matrix.rank_transpose, Matrix.rank_transpose] at h2
  omega

/-- **Lemma 3.3(ii), serial.** -/
theorem serial_generic_full_rank (hFR : FejerRieszHyp) (hQ : GQSPHyp) (hS : SardHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → Fin 2 → Fin 2 → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      (gateJ L tbl (fun i => Matrix.of (G i))).rank < 2 * L + 1} = 0 := by
  obtain ⟨G₀, hG₀, hrank⟩ := serial_full_rank_witness hFR hQ hS L tbl htbl
  exact genericity (gateJ L tbl) (serial_gramDet_poly L tbl) G₀ hG₀ hrank μ hμ

/-- **Lemma 3.3(ii), ancilla.** -/
theorem ancilla_generic_full_rank (hFR : FejerRieszHyp) (hQ : GQSPHyp) (hS : SardHyp) (L tbl : ℕ)
    (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ))
    (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      (ancillaJ L tbl (fun i => Matrix.of (G i))).rank < 2 * L + 1} = 0 := by
  obtain ⟨G₀, hG₀, hrank⟩ := ancilla_full_rank_witness hFR hQ hS L tbl htbl
  exact genericity (ancillaJ L tbl) (ancilla_gramDet_poly L tbl) G₀ hG₀ hrank μ hμ

end

end


/-! # Section 20: Lemma B.2 (stacked gates rescale the Riemannian step) -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 20. Lemma B.2: stacked gates rescale the Riemannian step -/

/-- Conjugating an orthonormal Pauli-type basis by one unitary leaves `Σ_a D(i P_a) P_a` unchanged. -/
theorem pauli_frame_invariant {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}
    (P : Fin K → Matrix n n ℂ)
    (hherm : ∀ a, (P a)ᴴ = P a) (htr : ∀ a, (P a).trace = 0)
    (horth : ∀ a b, (P a * P b).trace = if a = b then (Fintype.card n : ℂ) else 0)
    (hspan : ∀ X : Matrix n n ℂ, Xᴴ = X → X.trace = 0 →
      X = ∑ a, (((P a * X).trace).re / Fintype.card n : ℝ) • P a)
    (D : Matrix n n ℂ →ₗ[ℝ] ℝ) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ∑ a, D (Complex.I • (Uᴴ * P a * U)) • (Uᴴ * P a * U) = ∑ a, D (Complex.I • P a) • P a := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  set d : ℝ := (Fintype.card n : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos
  have hU1 : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  have hU2 : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  set Q : Fin K → Matrix n n ℂ := fun a => Uᴴ * P a * U with hQ
  have hQherm : ∀ a, (Q a)ᴴ = Q a := fun a => by
    simp only [hQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hherm, Matrix.mul_assoc]
  have hQtr : ∀ a, (Q a).trace = 0 := fun a => by
    simp only [hQ]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul, htr]
  have hQorth : ∀ a b, (Q a * Q b).trace = (P a * P b).trace := fun a b => by
    simp only [hQ]
    rw [show Uᴴ * P a * U * (Uᴴ * P b * U) = Uᴴ * (P a * P b) * U by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc U, hU2, Matrix.one_mul]]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
  set R : Matrix (Fin K) (Fin K) ℝ := fun a b => ((P b * Q a).trace).re / d with hR
  have hQexp : ∀ a, Q a = ∑ b, R a b • P b := fun a => hspan (Q a) (hQherm a) (hQtr a)
  have htrsmul : ∀ (r : ℝ) (M : Matrix n n ℂ), (r • M).trace = (r : ℂ) * M.trace := fun r M => by
    rw [Matrix.trace_smul, Complex.real_smul]
  have hRR : R * Rᵀ = 1 := by
    ext a b
    have h1 : (Q a * Q b).trace = (d : ℂ) * ∑ c, ((R a c * R b c : ℝ) : ℂ) := by
      rw [hQexp a, hQexp b, Finset.sum_mul]
      simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul, htrsmul, horth]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      push_cast [hd]
      ring
    have h3 : ((d * ∑ c, R a c * R b c : ℝ) : ℂ) = ((if a = b then d else 0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_sum, ← h1, hQorth, horth]
      split_ifs <;> simp [hd]
    have h4 := Complex.ofReal_injective h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    split_ifs with hab
    · rw [if_pos hab] at h4
      field_simp at h4
      linarith
    · rw [if_neg hab] at h4
      exact (mul_eq_zero.mp h4).resolve_left hdpos.ne'
  have hRtR : Rᵀ * R = 1 := mul_eq_one_comm.mp hRR
  have hcol : ∀ b c, ∑ a, R a b * R a c = if b = c then 1 else 0 := by
    intro b c
    have := congrFun (congrFun hRtR b) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.transpose_apply] using this
  have hDlin : ∀ a, D (Complex.I • Q a) = ∑ b, R a b * D (Complex.I • P b) := fun a => by
    rw [hQexp a, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_smul, smul_eq_mul]
  calc ∑ a, D (Complex.I • Q a) • Q a
      = ∑ a, ∑ b, ∑ c, (R a b * R a c * D (Complex.I • P b)) • P c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [hDlin a]
        conv_lhs => rw [hQexp a]
        rw [Finset.smul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_smul]
        congr 1; ring
    _ = ∑ b, ∑ c, ((∑ a, R a b * R a c) * D (Complex.I • P b)) • P c := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul, Finset.sum_smul]
    _ = ∑ b, D (Complex.I • P b) • P b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hcol, ite_mul, one_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

/-- Algebraic step: for an orthonormal Pauli-type basis `P` and any ℝ-linear `D`,
    `Σ_i Σ_a D(i B_iᴴ P_a B_i) B_iᴴ P_a B_i = t Σ_a D(i P_a) P_a`. -/
theorem stacked_gates_first_order {n : Type*} [Fintype n] [DecidableEq n] {K t : ℕ}
    (P : Fin K → Matrix n n ℂ)
    (hherm : ∀ a, (P a)ᴴ = P a) (htr : ∀ a, (P a).trace = 0)
    (horth : ∀ a b, (P a * P b).trace = if a = b then (Fintype.card n : ℂ) else 0)
    (hspan : ∀ X : Matrix n n ℂ, Xᴴ = X → X.trace = 0 →
      X = ∑ a, (((P a * X).trace).re / Fintype.card n : ℝ) • P a)
    (D : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (B : Fin t → Matrix n n ℂ) (hB : ∀ i, B i ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ a, D (Complex.I • ((B i)ᴴ * P a * B i)) • ((B i)ᴴ * P a * B i) =
      (t : ℝ) • ∑ a, D (Complex.I • P a) • P a := by
  have h := fun i => pauli_frame_invariant P hherm htr horth hspan D (B i) (hB i)
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]

/-- Right-trivialised gradient of the loss `ℓ` with respect to Pauli coordinate `a` of gate `i` of the block. -/
def gradGate {n : Type*} [Fintype n] [DecidableEq n] {K t : ℕ} (P : Fin K → Matrix n n ℂ)
    (V : Fin t → Matrix n n ℂ) (ℓ : (n → n → ℂ) → ℝ) (i : Fin t) (a : Fin K) : ℝ :=
  deriv (fun s => ℓ (Matrix.of.symm (blockProd t (Function.update V i (lieCurve (V i) (P a) s))))) 0

/-- Right-trivialised gradient with respect to Pauli coordinate `a` of the block itself. -/
def gradBlock {n : Type*} [Fintype n] [DecidableEq n] {K t : ℕ} (P : Fin K → Matrix n n ℂ)
    (V : Fin t → Matrix n n ℂ) (ℓ : (n → n → ℂ) → ℝ) (a : Fin K) : ℝ :=
  deriv (fun s => ℓ (Matrix.of.symm (lieCurve (blockProd t V) (P a) s))) 0

/-- Entrywise product rule for matrix curves. -/
theorem hasDerivAt_matrix_mul {n : Type*} [Fintype n] (A B : ℝ → Matrix n n ℂ) (A' B' : Matrix n n ℂ)
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) 0) (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) 0)
    (a b : n) : HasDerivAt (fun s => (A s * B s) a b) ((A' * B 0 + A 0 * B') a b) 0 := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun c _ => (hA a c).mul (hB c b)

/-- Product rule for a block: the derivative is the sum over gates of the block with that gate differentiated. -/
theorem blockProd_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ (t : ℕ) (M : Fin t → ℝ → Matrix n n ℂ) (M' : Fin t → Matrix n n ℂ),
      (∀ i a b, HasDerivAt (fun s => M i s a b) (M' i a b) 0) → ∀ a b,
      HasDerivAt (fun s => blockProd t (fun i => M i s) a b)
        ((∑ i, blockProd t (Function.update (fun j => M j 0) i (M' i))) a b) 0
  | 0, M, M', _, a, b => by
    simp only [blockProd, Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_apply]
    exact hasDerivAt_const _ _
  | t + 1, M, M', hM, a, b => by
    have ih := blockProd_hasDerivAt t (fun i => M (Fin.castSucc i)) (fun i => M' (Fin.castSucc i))
      (fun i => hM _)
    have h := hasDerivAt_matrix_mul (fun s => M (Fin.last t) s) (fun s => blockProd t (fun i => M (Fin.castSucc i) s))
      (M' (Fin.last t)) _ (hM _) ih a b
    have key : ∑ i, blockProd (t + 1) (Function.update (fun j => M j 0) i (M' i)) =
        M' (Fin.last t) * blockProd t (fun i => M (Fin.castSucc i) 0) +
          M (Fin.last t) 0 * ∑ i, blockProd t (Function.update (fun j => M (Fin.castSucc j) 0) i
            (M' (Fin.castSucc i))) := by
      rw [Fin.sum_univ_castSucc, add_comm, Matrix.mul_sum]
      congr 1
      · simp only [blockProd, Function.update_self]
        congr 1
        congr 1
        funext i
        rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hc : (fun k => Function.update (fun j => M j 0) (Fin.castSucc i) (M' (Fin.castSucc i))
            (Fin.castSucc k)) = Function.update (fun j => M (Fin.castSucc j) 0) i (M' (Fin.castSucc i)) :=
          Function.update_comp_eq_of_injective (fun j => M j 0) (Fin.castSucc_injective _) i _
        simp only [blockProd]
        rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne', hc]
    rw [key]
    exact h

/-- A block with gate `i` replaced: `blockProd t (update V i A) = U A D` with `D` unitary and `U V_i D` the block. -/
theorem blockProd_split_unitary {n : Type*} [Fintype n] [DecidableEq n] (t : ℕ) (V : Fin t → Matrix n n ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup n ℂ) (i : Fin t) :
    ∃ U D : Matrix n n ℂ, D ∈ Matrix.unitaryGroup n ℂ ∧
      (∀ A, blockProd t (Function.update V i A) = U * A * D) ∧ blockProd t V = U * V i * D := by
  obtain ⟨D, hD⟩ := blockProd_split (Matrix.unitaryGroup n ℂ) t V i
  obtain ⟨U, hU, hUS⟩ := hD V (fun _ _ => rfl)
  have hUu : U ∈ Matrix.unitaryGroup n ℂ := hUS fun j _ => hV j
  have hB : blockProd t (Function.update V i 1) ∈ Matrix.unitaryGroup n ℂ :=
    blockProd_mem _ t _ fun j => by
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact one_mem _
      · rw [Function.update_of_ne hj]; exact hV j
  rw [hU 1, mul_one] at hB
  have hU' : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hUu
  have hD' : D = star U * (U * D) := by rw [← mul_assoc, hU', one_mul]
  refine ⟨U, D, ?_, hU, ?_⟩
  · rw [hD']; exact mul_mem (Unitary.star_mem hUu) hB
  · rw [← hU (V i), Function.update_eq_self]

/-- **Lemma B.2.** If every gate is updated along a curve `γ_i` with `γ_i(0) = I` and first-order term
    `−i g_i · P` (for example `exp(−iη g_i · P)`), the block moves with first-order term `W (−i t g · P)`: to first
    order in `η` it agrees with `W exp(−i t η g · P)`. `P` is any orthonormal basis of the traceless Hermitian matrices
    (`tr(P_a P_b) = d δ_ab`), e.g. the non-identity Pauli words (`pauli_basis_props`, `pauliWord_basis_props`); the
    gradients are derivatives along `V_i (cos s · I + i sin s · P_a)`, which has the same first-order term as
    `V_i exp(i s P_a)`. -/
theorem stacked_gates_rescale {n : Type*} [Fintype n] [DecidableEq n] {K t : ℕ} (P : Fin K → Matrix n n ℂ)
    (hherm : ∀ a, (P a)ᴴ = P a) (htr : ∀ a, (P a).trace = 0)
    (horth : ∀ a b, (P a * P b).trace = if a = b then (Fintype.card n : ℂ) else 0)
    (hspan : ∀ X : Matrix n n ℂ, Xᴴ = X → X.trace = 0 →
      X = ∑ a, (((P a * X).trace).re / Fintype.card n : ℝ) • P a)
    (V : Fin t → Matrix n n ℂ) (hV : ∀ i, V i ∈ Matrix.unitaryGroup n ℂ)
    (ℓ : (n → n → ℂ) → ℝ) (hℓ : DifferentiableAt ℝ ℓ (Matrix.of.symm (blockProd t V)))
    (γ : Fin t → ℝ → Matrix n n ℂ) (hγ0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i a b, HasDerivAt (fun η => γ i η a b)
      ((-(Complex.I • ∑ c, (gradGate P V ℓ i c : ℂ) • P c)) a b) 0) (a b : n) :
    HasDerivAt (fun η => blockProd t (fun i => V i * γ i η) a b)
      ((blockProd t V * (-(Complex.I • ((t : ℂ) • ∑ c, (gradBlock P V ℓ c : ℂ) • P c)))) a b) 0 := by
  set W := blockProd t V with hW
  set Lf := fderiv ℝ ℓ (Matrix.of.symm W) with hLf
  have hLfd : HasFDerivAt ℓ Lf (Matrix.of.symm W) := hℓ.hasFDerivAt
  -- chain rule along matrix curves through `W`
  have chain : ∀ (C : ℝ → Matrix n n ℂ) (C' : Matrix n n ℂ), C 0 = W →
      (∀ a b, HasDerivAt (fun s => C s a b) (C' a b) 0) →
      HasDerivAt (fun s => ℓ (Matrix.of.symm (C s))) (Lf (Matrix.of.symm C')) 0 := by
    intro C C' hC0 hC
    have hc : HasDerivAt (fun s => Matrix.of.symm (C s)) (Matrix.of.symm C') 0 := by
      rw [hasDerivAt_pi]; intro a
      rw [hasDerivAt_pi]; intro b
      exact hC a b
    have h0 : Matrix.of.symm (C 0) = Matrix.of.symm W := by rw [hC0]
    rw [← h0] at hLfd
    exact hLfd.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s => Matrix.of.symm (C s)) hc
  -- the ℝ-linear functional `D X = Lf (W X)`
  let Dl : Matrix n n ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun X => Lf (Matrix.of.symm (W * X))
      map_add' := fun X Y => by
        rw [Matrix.mul_add]
        exact map_add Lf _ _
      map_smul' := fun r X => by
        rw [Matrix.mul_smul]
        exact map_smul Lf r _ }
  have hDl : ∀ X, Dl X = Lf (Matrix.of.symm (W * X)) := fun X => rfl
  choose U Dm hDu hUD hWsplit using fun i => blockProd_split_unitary t V hV i
  have hDD : ∀ i, Dm i * (Dm i)ᴴ = 1 := fun i => (Matrix.mem_unitaryGroup_iff).1 (hDu i)
  have hconj : ∀ i X, U i * (V i * X) * Dm i = W * ((Dm i)ᴴ * X * Dm i) := by
    intro i X
    rw [hW, hWsplit i]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Dm i) (Dm i)ᴴ, hDD i, Matrix.one_mul]
  -- the gate gradients
  have hgate : ∀ i c, gradGate P V ℓ i c = Dl (Complex.I • ((Dm i)ᴴ * P c * Dm i)) := by
    intro i c
    unfold gradGate
    have hcurve : ∀ a b, HasDerivAt (fun s => blockProd t (Function.update V i (lieCurve (V i) (P c) s)) a b)
        ((U i * (V i * (Complex.I • P c)) * Dm i) a b) 0 := by
      intro a b
      simp only [hUD i]
      have h1 := hasDerivAt_matrix_mul (fun s => U i * lieCurve (V i) (P c) s) (fun _ => Dm i)
        (U i * (V i * (Complex.I • P c))) 0
        (fun a b => by
          have h2 := hasDerivAt_matrix_mul (fun _ => U i) (fun s => lieCurve (V i) (P c) s) 0
            (V i * (Complex.I • P c)) (fun _ _ => hasDerivAt_const _ _)
            (fun a b => lieCurve_hasDerivAt (V i) (P c) a b) a b
          simpa using h2)
        (fun _ _ => hasDerivAt_const _ _) a b
      simpa using h1
    have h0 : blockProd t (Function.update V i (lieCurve (V i) (P c) 0)) = W := by
      rw [lieCurve_zero, Function.update_eq_self]
    rw [(chain _ _ h0 hcurve).deriv, hconj, hDl, Matrix.mul_smul, Matrix.smul_mul]
  have hblock : ∀ c, gradBlock P V ℓ c = Dl (Complex.I • P c) := by
    intro c
    unfold gradBlock
    have hcurve : ∀ a b, HasDerivAt (fun s => lieCurve W (P c) s a b) ((W * (Complex.I • P c)) a b) 0 :=
      fun a b => lieCurve_hasDerivAt W (P c) a b
    rw [(chain _ _ (lieCurve_zero W (P c)) hcurve).deriv, hDl]
  -- derivative of the updated block
  set γ' : Fin t → Matrix n n ℂ := fun i => -(Complex.I • ∑ c, (gradGate P V ℓ i c : ℂ) • P c) with hγ'
  have hM : ∀ i a b, HasDerivAt (fun η => (V i * γ i η) a b) ((V i * γ' i) a b) 0 := by
    intro i a b
    have h := hasDerivAt_matrix_mul (fun _ => V i) (fun η => γ i η) 0 (γ' i)
      (fun _ _ => hasDerivAt_const _ _) (fun a b => hγ i a b) a b
    simpa using h
  have hd := blockProd_hasDerivAt t (fun i η => V i * γ i η) (fun i => V i * γ' i) hM a b
  have hM0 : (fun j => V j * γ j 0) = V := by funext j; rw [hγ0, Matrix.mul_one]
  simp only [hM0] at hd
  convert hd using 2
  have hsum : ∑ i, blockProd t (Function.update V i (V i * γ' i)) =
      W * ∑ i, (Dm i)ᴴ * γ' i * Dm i := by
    rw [Matrix.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hUD i, hconj]
  rw [hsum]
  congr 1
  have hfo := stacked_gates_first_order P hherm htr horth hspan Dl Dm hDu
  simp only [hγ', hgate, hblock]
  have hR : ∀ (r : ℝ) (M : Matrix n n ℂ), (r : ℂ) • M = r • M := fun r M => Complex.coe_smul r M
  simp only [hR]
  have key : ∀ x, (Dm x)ᴴ * -(Complex.I • ∑ c, Dl (Complex.I • ((Dm x)ᴴ * P c * Dm x)) • P c) * Dm x =
      -(Complex.I • ∑ c, Dl (Complex.I • ((Dm x)ᴴ * P c * Dm x)) • ((Dm x)ᴴ * P c * Dm x)) := by
    intro x
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_neg_distrib, ← Finset.smul_sum, hfo,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]


/-- The one-qubit Pauli words `X, Y, Z` satisfy the basis hypotheses of `stacked_gates_rescale`. -/
theorem pauli_basis_props :
    (∀ a, (pauli a)ᴴ = pauli a) ∧ (∀ a, (pauli a).trace = 0) ∧
    (∀ a b, (pauli a * pauli b).trace = if a = b then (Fintype.card (Fin 2) : ℂ) else 0) ∧
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, Xᴴ = X → X.trace = 0 →
      X = ∑ a, (((pauli a * X).trace).re / Fintype.card (Fin 2) : ℝ) • pauli a) := by
  refine ⟨pauli_herm, ?_, ?_, ?_⟩
  · intro a; fin_cases a <;> simp [pauli, pauli1, Matrix.trace_fin_two]
  · intro a b; fin_cases a <;> fin_cases b <;>
      simp [pauli, pauli1, Matrix.trace_fin_two] <;> norm_num
  · intro X hX htr
    have e : ∀ a b, (starRingEnd ℂ) (X b a) = X a b := fun a b => by
      have := congrFun (congrFun hX a) b
      simpa [conjTranspose_apply] using this
    have e00 := e 0 0
    have e11 := e 1 1
    have e01 := e 0 1
    rw [Matrix.trace_fin_two] at htr
    rw [Complex.ext_iff] at e00 e11 e01 htr
    simp at e00 e11 e01 htr
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Fin.sum_univ_three, pauli, pauli1, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.ext_iff] <;> constructor <;> linarith

/-- The 15 non-identity two-qubit Pauli words, indexed by `Fin 15`. -/
def pauliWordFin (a : Fin (Fintype.card PWord)) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliWord ((Fintype.equivFin PWord).symm a)

/-- Each one-qubit Pauli matrix (including the identity) is Hermitian. -/
theorem pauli1_herm (i : Fin 4) : (pauli1 i)ᴴ = pauli1 i := by
  ext a b; fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [pauli1, Matrix.conjTranspose_apply]

/-- Traces of the one-qubit Pauli matrices: `tr σ₀ = 2`, `tr σ_a = 0` otherwise. -/
theorem pauli1_trace (i : Fin 4) : (pauli1 i).trace = if i = 0 then 2 else 0 := by
  fin_cases i <;> simp [pauli1, Matrix.trace_fin_two]

/-- Orthogonality of the one-qubit Pauli matrices: `tr(σ_i σ_k) = 2 δ_ik`. -/
theorem pauli1_mul_trace (i k : Fin 4) : (pauli1 i * pauli1 k).trace = if i = k then 2 else 0 := by
  fin_cases i <;> fin_cases k <;> simp [pauli1, Matrix.trace_fin_two] <;> norm_num

/-- Completeness of the 16 two-qubit Pauli words `σ_i ⊗ σ_j`: `X = Σ tr(P X)/4 · P` for every `4 × 4` matrix. -/
theorem pauli2_complete (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    X = ∑ q : Fin 4 × Fin 4, ((Matrix.kronecker (pauli1 q.1) (pauli1 q.2) * X).trace / 4) •
      Matrix.kronecker (pauli1 q.1) (pauli1 q.2) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
    smul_eq_mul]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pauli1] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The two-qubit Pauli words satisfy the basis hypotheses of `stacked_gates_rescale`. -/
theorem pauliWord_basis_props :
    (∀ a, (pauliWordFin a)ᴴ = pauliWordFin a) ∧ (∀ a, (pauliWordFin a).trace = 0) ∧
    (∀ a b, (pauliWordFin a * pauliWordFin b).trace = if a = b then (Fintype.card (Fin 2 × Fin 2) : ℂ) else 0) ∧
    (∀ X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, Xᴴ = X → X.trace = 0 →
      X = ∑ a, (((pauliWordFin a * X).trace).re / Fintype.card (Fin 2 × Fin 2) : ℝ) • pauliWordFin a) := by
  set e := Fintype.equivFin PWord with he
  have hK : ∀ i j : Fin 4, Matrix.kronecker (pauli1 i) (pauli1 j) =
      Matrix.kroneckerMap (· * ·) (pauli1 i) (pauli1 j) := fun _ _ => rfl
  have hherm : ∀ q : Fin 4 × Fin 4, (Matrix.kronecker (pauli1 q.1) (pauli1 q.2))ᴴ =
      Matrix.kronecker (pauli1 q.1) (pauli1 q.2) := fun q => by
    rw [hK, Matrix.conjTranspose_kronecker, pauli1_herm, pauli1_herm]
  have hmul : ∀ q r : Fin 4 × Fin 4, (Matrix.kronecker (pauli1 q.1) (pauli1 q.2) *
      Matrix.kronecker (pauli1 r.1) (pauli1 r.2)).trace = if q = r then 4 else 0 := by
    intro q r
    rw [hK, hK, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, pauli1_mul_trace, pauli1_mul_trace]
    obtain ⟨i, j⟩ := q; obtain ⟨k, l⟩ := r
    by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2]; norm_num
  have htr0 : ∀ p : PWord, (pauliWord p).trace = 0 := by
    rintro ⟨⟨i, j⟩, h⟩
    show (Matrix.kronecker (pauli1 i) (pauli1 j)).trace = 0
    rw [hK, Matrix.trace_kronecker, pauli1_trace, pauli1_trace]
    by_cases hi : i = 0
    · subst hi; have : j ≠ 0 := fun hj => h (by rw [hj]); simp [this]
    · simp [hi]
  refine ⟨fun a => hherm _, fun a => htr0 _, fun a b => ?_, fun X hX htr => ?_⟩
  · show (Matrix.kronecker (pauli1 (e.symm a).1.1) (pauli1 (e.symm a).1.2) *
      Matrix.kronecker (pauli1 (e.symm b).1.1) (pauli1 (e.symm b).1.2)).trace = _
    rw [hmul]
    have : ((e.symm a).1 = (e.symm b).1) ↔ a = b := by
      rw [← Subtype.ext_iff, e.symm.injective.eq_iff]
    simp only [this, Fintype.card_prod, Fintype.card_fin]
    norm_num
  · set g : Fin 4 × Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun q =>
      (((Matrix.kronecker (pauli1 q.1) (pauli1 q.2) * X).trace).re / 4 : ℝ) •
        Matrix.kronecker (pauli1 q.1) (pauli1 q.2) with hg
    have h1 : ∑ a, (((pauliWordFin a * X).trace).re / Fintype.card (Fin 2 × Fin 2) : ℝ) • pauliWordFin a =
        ∑ p : PWord, g p.1 := by
      rw [← e.symm.sum_comp]
      simp only [Fintype.card_prod, Fintype.card_fin, hg, pauliWordFin, pauliWord, he]
      norm_num
    have h2 : ∑ p : PWord, g p.1 = ∑ q ∈ Finset.univ.erase (0, 0), g q :=
      (Finset.sum_subtype _ (fun q => by simp) g).symm
    have h3 : ∑ q ∈ Finset.univ.erase (0, 0), g q = ∑ q, g q := by
      apply Finset.sum_erase
      simp [hg, pauli1, htr]
    rw [h1, h2, h3]
    conv_lhs => rw [pauli2_complete X]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hg]
    rw [← Complex.coe_smul]
    congr 1
    have hreal : (starRingEnd ℂ) ((Matrix.kronecker (pauli1 q.1) (pauli1 q.2) * X).trace) =
        (Matrix.kronecker (pauli1 q.1) (pauli1 q.2) * X).trace := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hherm,
        Matrix.trace_mul_comm]
    have := Complex.conj_eq_iff_re.mp hreal
    push_cast
    rw [this]


/-! ## 21. Proposition 4.4: tangent count

`T` = real span of the tangent-coefficient functions x ↦ h_j(x) over all Lie-algebra coordinates j, in the frame
e_r(x) = U(x)|r⟩ (for one qubit, the frame Tψ of Lemma 4.2 up to sign). Since the h_j are trigonometric polynomials of
degree ≤ L, dim T equals the rank of the matrix H of Eq. (2). -/

/-- Serial circuit: h_j(x) = ⟨Tψ(x), ∂_jψ(x)⟩ for the Lie-algebra coordinate j = (block, gate, Pauli word). -/
def serialTangentFn (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (j : SIdx L tbl) : ℝ → ℂ :=
  gateH L tbl G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2))

/-- Real dimension of the span of the serial tangent-coefficient functions. -/
def serialTangentRank (L tbl : ℕ) (G : Gates L tbl (Fin 2)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (serialTangentFn L tbl G)))

/-- The ancilla circuit as a matrix: `U(x) = W_L (R_X(x) ⊗ I) W_{L−1} ⋯ (R_X(x) ⊗ I) W_0`. -/
def ancillaUnitary : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) → ℝ →
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | 0, W, _ => W 0
  | L + 1, W, x => W (Fin.last (L + 1)) *
      (Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ) * ancillaUnitary L (fun i => W (Fin.castSucc i)) x)

/-- Blocks of the ancilla circuit with `tbl` gates each. -/
def ancillaBlocks (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ℓ => blockProd tbl (fun g => G (ℓ, g))

/-- The three frame indices r ≠ |00⟩. -/
def frameIdx : Fin 3 → Fin 2 × Fin 2 := ![(0, 1), (1, 0), (1, 1)]

/-- Ancilla circuit: h_j(x) = (⟨U(x)|r⟩, ∂_jψ(x)⟩)_{r ≠ 00}. -/
def ancillaTangentFn (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) : ℝ → Fin 3 → ℂ :=
  fun x r => dotProduct (star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) x a (frameIdx r)))
    (deriv (fun s => ancillaState L (ancillaBlocks L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s))) x) 0)

/-- Real dimension of the span of the ancilla tangent-coefficient functions. -/
def ancillaTangentRank (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (ancillaTangentFn L tbl G)))

/-! ### Helper lemmas for Proposition 4.4 -/
theorem cos_sin_comb_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : E) :
    HasDerivAt (fun s : ℝ => (Real.cos s : ℂ) • u + (Real.sin s : ℂ) • v) v 0 := by
  have h1 := ((Real.hasDerivAt_cos 0).ofReal_comp).smul_const u
  have h2 := ((Real.hasDerivAt_sin 0).ofReal_comp).smul_const v
  convert h1.add h2 using 1
  simp

theorem serialTangentFn_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (j : SIdx L tbl) (x : ℝ) :
    serialTangentFn L tbl G j x = ip (T (gateState L tbl G x))
      (gateState L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauli j.2.2))) x) := by
  unfold serialTangentFn gateH gateTangent
  congr 1
  have e : (fun s => gateState L tbl (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauli j.2.2) s)) x) =
      fun s : ℝ => (Real.cos s : ℂ) • gateState L tbl G x + (Real.sin s : ℂ) •
        gateState L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauli j.2.2))) x := by
    funext s
    rw [lieCurve_eq_comb, gateState_perturb_linear, perturb_self]
  rw [e]
  exact (cos_sin_comb_hasDerivAt _ _).deriv

theorem ancillaTangentFn_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) (x : ℝ) (r : Fin 3) :
    ancillaTangentFn L tbl G j x r =
      star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
        ancillaState L (ancillaBlocks L tbl
          (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x := by
  unfold ancillaTangentFn
  congr 1
  have e : (fun s => ancillaState L (ancillaBlocks L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s))) x) =
      fun s : ℝ => (Real.cos s : ℂ) • ancillaState L (ancillaBlocks L tbl G) x + (Real.sin s : ℂ) •
        ancillaState L (ancillaBlocks L tbl
          (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x := by
    funext s
    unfold ancillaBlocks
    rw [lieCurve_eq_comb, ancillaGateState_perturb_linear, perturb_self]
  rw [e]
  exact (cos_sin_comb_hasDerivAt _ _).deriv

theorem gram_det_ne_zero_of_linInd {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ]
    (A : Matrix ρ κ ℝ) (h : LinearIndependent ℝ (fun a => A a)) : (A * Aᵀ).det ≠ 0 := by
  have hker : ∀ v, (A * Aᵀ) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h1 : (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) = 0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        Matrix.mulVec_mulVec, hv, zero_dotProduct]
    have h2 : Aᵀ *ᵥ v = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg ((Aᵀ *ᵥ v) i))).1 h1 k
        (Finset.mem_univ _)
      simpa using this
    rw [Fintype.linearIndependent_iff] at h
    funext a
    refine h v ?_ a
    funext k
    have := congrFun h2 k
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
  have hinj : Function.Injective (A * Aᵀ).mulVec := by
    intro v w hvw
    have := hker (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    exact sub_eq_zero.1 this
  have hu := Matrix.mulVec_injective_iff_isUnit.1 hinj
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem linInd_of_gram_det_ne_zero {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ]
    (A : Matrix ρ κ ℝ) (h : (A * Aᵀ).det ≠ 0) : LinearIndependent ℝ (fun a => A a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hu : IsUnit (A * Aᵀ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hu
  have h0 : (A * Aᵀ) *ᵥ g = (A * Aᵀ) *ᵥ 0 := by
    rw [Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
    have : Aᵀ *ᵥ g = 0 := by
      funext k
      have := congrFun hg k
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
    rw [this, Matrix.mulVec_zero]
  intro a
  exact congrFun (hinj h0) a

open MeasureTheory in
theorem tangent_rank_generic_of_witness {ι n J ρ κ W : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [Finite J] [Fintype ρ] [DecidableEq ρ] [Fintype κ] [AddCommGroup W] [Module ℝ W]
    (F : (ι → Matrix n n ℂ) → J → W) (E : W →ₗ[ℝ] (κ → ℝ)) (c : ρ → J)
    (hpoly : ∀ a k, IsRPoly (fun G => E (F G (c a)) k))
    (G₀ : ι → Matrix n n ℂ) (hG₀ : ∀ i, G₀ i ∈ Matrix.specialUnitaryGroup n ℂ)
    (hwit : LinearIndependent ℝ (fun a => E (F G₀ (c a))))
    (μ : MeasureTheory.Measure (ι → n → n → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup n ℂ) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range (F (fun i => Matrix.of (G i))))) <
        Fintype.card ρ} = 0 := by
  set A : (ι → Matrix n n ℂ) → Matrix ρ κ ℝ := fun G a k => E (F G (c a)) k with hA
  obtain ⟨q, hq⟩ := IsRPoly.det (fun G => A G * (A G)ᵀ) (fun a b =>
    (IsRPoly.sum Finset.univ fun k _ => (hpoly a k).mul (hpoly b k)).congr fun G => by
      simp [A, Matrix.mul_apply])
  have hne : MvPolynomial.eval (reIm G₀) q ≠ 0 := by
    rw [← hq]
    exact gram_det_ne_zero_of_linInd _ hwit
  refine measure_mono_null ?_ (hμ q ⟨G₀, hG₀, hne⟩)
  rintro G ⟨hSU, hlt⟩
  refine ⟨hSU, ?_⟩
  by_contra h
  rw [← hq] at h
  simp only at h
  have hli := linInd_of_gram_det_ne_zero _ h
  set G' : ι → Matrix n n ℂ := fun i => Matrix.of (G i)
  have hli' : LinearIndependent ℝ (fun a => F G' (c a)) := LinearIndependent.of_comp E hli
  set S := Submodule.span ℝ (Set.range (F G'))
  haveI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hli'' : LinearIndependent ℝ (fun a => (⟨F G' (c a), Submodule.subset_span ⟨c a, rfl⟩⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hli'
  exact absurd hli''.fintype_card_le_finrank (not_le.2 hlt)

theorem herm_entries {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Yᴴ = Y) :
    Y 1 0 = (starRingEnd ℂ) (Y 0 1) ∧ (Y 0 0).im = 0 ∧ (Y 1 1).im = 0 := by
  have e : ∀ a b, (starRingEnd ℂ) (Y b a) = Y a b := fun a b => by
    have := congrFun (congrFun hY a) b
    simpa [conjTranspose_apply] using this
  refine ⟨(e 1 0).symm, ?_, ?_⟩
  · have := congrArg Complex.im (e 0 0); simp at this; linarith
  · have := congrArg Complex.im (e 1 1); simp at this; linarith

theorem RXm_real (x : ℝ) : RXm x = !![((Real.cos (x / 2) : ℝ) : ℂ), -Complex.I * ((Real.sin (x / 2) : ℝ) : ℂ);
    -Complex.I * ((Real.sin (x / 2) : ℝ) : ℂ), ((Real.cos (x / 2) : ℝ) : ℂ)] := by
  simp only [RXm, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_ofNat]

theorem RXm_conj_herm {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Yᴴ = Y) (x : ℝ) :
    (RXm x)ᴴ * (Complex.I • Y) * RXm x =
      Complex.I • ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0)) +
      ((Real.cos x * (-(Y 0 1).im) + Real.sin x * (((Y 0 0).re - (Y 1 1).re) / 2) : ℝ) : ℂ) •
        (Complex.I • pauli 1) +
      ((Real.cos x * (((Y 0 0).re - (Y 1 1).re) / 2) - Real.sin x * (-(Y 0 1).im) : ℝ) : ℂ) •
        (Complex.I • pauli 2) := by
  obtain ⟨h10, h00, h11⟩ := herm_entries hY
  have hc : Real.cos x = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 := by
    have := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (x / 2)
  have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (x / 2)
  rw [RXm_real, hc, hs]
  generalize Real.cos (x / 2) = c at *
  generalize Real.sin (x / 2) = s at *
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pauli, pauli1, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, h10,
      Complex.ext_iff, h00, h11, vecMul, dotProduct, sq] <;> constructor <;> first | linear_combination (0) * h1 | linear_combination (((Y 0 0).re + (Y 1 1).re) / 2) * h1 | linear_combination (-(((Y 0 0).re + (Y 1 1).re) / 2)) * h1 | linear_combination ((Y 0 1).re) * h1


theorem herm_pauli_decomp {W : Matrix (Fin 2) (Fin 2) ℂ} (hW : Wᴴ = W) :
    W = ((W 0 0 + W 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (((W 0 1).re : ℝ) : ℂ) • pauli 0 +
      ((-(W 0 1).im : ℝ) : ℂ) • pauli 1 + ((((W 0 0).re - (W 1 1).re) / 2 : ℝ) : ℂ) • pauli 2 := by
  obtain ⟨h10, h00, h11⟩ := herm_entries hW
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pauli, pauli1, Complex.ext_iff, h10, h00, h11] <;> ring



/-- State after the first `k` blocks and `k` encodings, for ℕ-indexed blocks `B`. -/
def preState (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : ℕ → ℝ → Fin 2 → ℂ
  | 0, _ => ![1, 0]
  | k + 1, x => RXm x *ᵥ (B k *ᵥ preState B k x)

theorem serialState_eq_preState : ∀ (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ), (∀ k : Fin (L + 1), B k = V k) →
    ∀ x, serialState L V x = V (Fin.last L) *ᵥ preState B L x
  | 0, V, B, _, x => rfl
  | L + 1, V, B, hB, x => by
    simp only [serialState]
    rw [serialState_eq_preState L (fun i => V (Fin.castSucc i)) B (fun k => hB k.castSucc) x]
    simp only [preState]
    congr 2
    rw [← hB (Fin.last L).castSucc]
    rfl

theorem serialState_update_preState : ∀ (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ), (∀ k : Fin (L + 1), B k = V k) →
    (∀ i, V i ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) → ∀ ℓ : Fin (L + 1),
    ∃ Down : ℝ → Matrix (Fin 2) (Fin 2) ℂ, (∀ x, Down x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      ∀ M x, serialState L (Function.update V ℓ M) x = Down x *ᵥ (M *ᵥ preState B ℓ x)
  | 0, V, B, _, _, ℓ => by
    obtain rfl : ℓ = 0 := Fin.fin_one_eq_zero ℓ
    refine ⟨fun _ => 1, fun _ => one_mem _, fun M x => ?_⟩
    simp [serialState, preState]
  | L + 1, V, B, hB, hV, ℓ => by
    by_cases hℓ : ℓ = Fin.last (L + 1)
    · subst hℓ
      refine ⟨fun _ => 1, fun _ => one_mem _, fun M x => ?_⟩
      simp only [serialState, Function.update_self, Matrix.one_mulVec]
      have hc : (fun i => Function.update V (Fin.last (L + 1)) M (Fin.castSucc i)) =
          fun i => V (Fin.castSucc i) := by
        funext i; exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
      rw [hc, serialState_eq_preState L _ B (fun k => hB k.castSucc) x]
      simp only [preState, Fin.val_last]
      congr 3
      exact (hB (Fin.last L).castSucc).symm
    · obtain ⟨ℓ', rfl⟩ := Fin.exists_castSucc_eq.mpr hℓ
      obtain ⟨Down, hDS, hDown⟩ := serialState_update_preState L (fun i => V (Fin.castSucc i)) B
        (fun k => hB k.castSucc) (fun i => hV _) ℓ'
      refine ⟨fun x => V (Fin.last (L + 1)) * RXm x * Down x,
        fun x => mul_mem (mul_mem (hV _) (RXm_mem_SU2 x)) (hDS x), fun M x => ?_⟩
      have hc : (fun i => Function.update V (Fin.castSucc ℓ') M (Fin.castSucc i)) =
          Function.update (fun i => V (Fin.castSucc i)) ℓ' M :=
        Function.update_comp_eq_of_injective V (Fin.castSucc_injective _) ℓ' M
      simp only [serialState]
      rw [Function.update_of_ne (Fin.castSucc_lt_last ℓ').ne', hc, hDown]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Fin.val_castSucc]


/-- ℕ-indexed blocks of a serial circuit (identity past the last block). -/
def serialBlk (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h : k < L + 1 then blockProd tbl (fun g => G (⟨k, h⟩, g)) else 1

theorem serialBlk_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (k : Fin (L + 1)) :
    serialBlk L tbl G k = blockProd tbl (fun g => G (k, g)) := by
  simp [serialBlk, k.2]

theorem serialBlk_mem (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (k : ℕ) :
    serialBlk L tbl G k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold serialBlk
  split_ifs
  · exact blockProd_mem _ tbl _ fun g => hG _
  · exact one_mem _

/-- `⟨Tφ, Mφ⟩` along the state `φ = preState B ℓ x`. -/
def gfun (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) : ℂ :=
  ip (T (preState B ℓ x)) (M *ᵥ preState B ℓ x)

theorem gfun_add (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (M N : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gfun B ℓ (M + N) x = gfun B ℓ M x + gfun B ℓ N x := by
  simp only [gfun, ip, Matrix.add_mulVec, Pi.add_apply]; ring

theorem gfun_smul (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gfun B ℓ (c • M) x = c * gfun B ℓ M x := by
  simp only [gfun, ip, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]; ring

theorem gfun_one (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (x : ℝ) : gfun B ℓ 1 x = 0 := by
  simp only [gfun, ip, T, Matrix.one_mulVec]; simp; ring

theorem gfun_zero (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gfun B 0 M x = M 1 0 := by
  simp [gfun, preState, ip, T, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem unitary_mul_star {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.specialUnitaryGroup n ℂ) : U * Uᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff).1 hU.1

theorem unitary_star_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.specialUnitaryGroup n ℂ) : Uᴴ * U = 1 :=
  (Matrix.mem_unitaryGroup_iff').1 hU.1

/-- `⟨T(Wφ), M Wφ⟩ = ⟨Tφ, WᴴMW φ⟩` for `W ∈ SU(2)`. -/
theorem ip_T_conj (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin 2 → ℂ) :
    ip (T (W *ᵥ φ)) (M *ᵥ (W *ᵥ φ)) = ip (T φ) ((Wᴴ * M * W) *ᵥ φ) := by
  have h : M *ᵥ (W *ᵥ φ) = W *ᵥ ((Wᴴ * M * W) *ᵥ φ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      unitary_mul_star hW, Matrix.one_mul]
  rw [h, T_mulVec_SU2 W hW, ip_unitary W hW.1]

theorem gfun_succ (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ)
    (hB : B ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gfun B (ℓ + 1) M x = gfun B ℓ ((B ℓ)ᴴ * ((RXm x)ᴴ * M * RXm x) * B ℓ) x := by
  unfold gfun
  simp only [preState]
  rw [Matrix.mulVec_mulVec, ip_T_conj _ (mul_mem (RXm_mem_SU2 x) hB)]
  congr 2
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem serialTangentFn_eq_gfun (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G)
    (i : Fin (L + 1) × Fin tbl) :
    ∃ D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ a x,
      serialTangentFn L tbl G (i.1, i.2, a) x =
        gfun (serialBlk L tbl G) i.1 (Dᴴ * (Complex.I • pauli a) * D) x := by
  obtain ⟨U, D, hU, hD, hUD⟩ := gate_blocks_update G i
  set Vb : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ := fun ℓ => blockProd tbl (fun g => G (ℓ, g)) with hVbdef
  have hVb : Vb i.1 = U * G i * D := by
    have := congrFun (hUD (G i)) i.1
    rw [perturb_self] at this
    simpa using this
  have hVbS : ∀ ℓ, Vb ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    fun ℓ => blockProd_mem _ tbl _ fun g => hG _
  obtain ⟨Down, hDS, hDown⟩ := serialState_update_preState L Vb (serialBlk L tbl G)
    (fun k => serialBlk_eq L tbl G k) hVbS i.1
  refine ⟨D, hD hG, fun a x => ?_⟩
  rw [serialTangentFn_eq]
  have e1 : gateState L tbl G x = serialState L (Function.update Vb i.1 (Vb i.1)) x := by
    rw [Function.update_eq_self]; rfl
  have e2 : gateState L tbl (perturb G (i.1, i.2) (G (i.1, i.2) * (Complex.I • pauli a))) x =
      serialState L (Function.update Vb i.1 (U * (G i * (Complex.I • pauli a)) * D)) x := by
    unfold gateState
    rw [← hUD]
  rw [e1, e2, hDown, hDown, gauge_invariance _ (hDS x)]
  unfold gfun
  set φ := preState (serialBlk L tbl G) (↑i.1) x
  have h3 : (U * (G i * (Complex.I • pauli a)) * D) *ᵥ φ =
      Vb i.1 *ᵥ ((Dᴴ * (Complex.I • pauli a) * D) *ᵥ φ) := by
    rw [Matrix.mulVec_mulVec, hVb]
    congr 1
    calc U * (G i * (Complex.I • pauli a)) * D = U * G i * (D * Dᴴ) * (Complex.I • pauli a) * D := by
          rw [unitary_mul_star (hD hG)]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3, T_mulVec_SU2 _ (hVbS _), ip_unitary _ (hVbS _).1]


theorem conj_herm {D Z : Matrix (Fin 2) (Fin 2) ℂ} (hZ : Zᴴ = Z) : (D * Z * Dᴴ)ᴴ = D * Z * Dᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hZ,
    Matrix.mul_assoc]

/-- For Hermitian `Z`, the function `x ↦ ⟨Tφ_ℓ, iZ φ_ℓ⟩` is a real combination of the tangent-coefficient
    functions of the first gate of block `ℓ`. -/
theorem herm_mem_block_span (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2)) (hG : InSU G)
    (ℓ : Fin (L + 1)) {Z : Matrix (Fin 2) (Fin 2) ℂ} (hZ : Zᴴ = Z) :
    (fun x => gfun (serialBlk L tbl G) ℓ (Complex.I • Z) x) ∈
      Submodule.span ℝ (Set.range fun a : Fin 3 => serialTangentFn L tbl G (ℓ, ⟨0, htbl⟩, a)) := by
  obtain ⟨D, hD, hfun⟩ := serialTangentFn_eq_gfun L tbl G hG (ℓ, ⟨0, htbl⟩)
  set W := D * Z * Dᴴ with hW
  have hWh : Wᴴ = W := conj_herm hZ
  have hdec := herm_pauli_decomp hWh
  have hZW : Complex.I • Z = Dᴴ * (Complex.I • W) * D := by
    rw [hW, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc, unitary_star_mul hD, Matrix.one_mul]
    rw [Matrix.mul_assoc, unitary_star_mul hD, Matrix.mul_one]
  set S := Submodule.span ℝ (Set.range fun a : Fin 3 => serialTangentFn L tbl G (ℓ, ⟨0, htbl⟩, a))
  have hmem : ∀ a : Fin 3, (fun x => gfun (serialBlk L tbl G) ℓ (Dᴴ * (Complex.I • pauli a) * D) x) ∈ S := by
    intro a
    have : (fun x => gfun (serialBlk L tbl G) ℓ (Dᴴ * (Complex.I • pauli a) * D) x) =
        serialTangentFn L tbl G (ℓ, ⟨0, htbl⟩, a) := by funext x; rw [hfun]
    rw [this]; exact Submodule.subset_span ⟨a, rfl⟩
  have key : (fun x => gfun (serialBlk L tbl G) ℓ (Complex.I • Z) x) =
      (W 0 1).re • (fun x => gfun (serialBlk L tbl G) ℓ (Dᴴ * (Complex.I • pauli 0) * D) x) +
      (-(W 0 1).im) • (fun x => gfun (serialBlk L tbl G) ℓ (Dᴴ * (Complex.I • pauli 1) * D) x) +
      (((W 0 0).re - (W 1 1).re) / 2) •
        (fun x => gfun (serialBlk L tbl G) ℓ (Dᴴ * (Complex.I • pauli 2) * D) x) := by
    funext x
    rw [hZW]
    conv_lhs => rw [hdec]
    simp only [smul_add, Matrix.mul_add, Matrix.add_mul, gfun_add, Pi.add_apply, Pi.smul_apply]
    rw [smul_comm Complex.I ((W 0 0 + W 1 1) / 2), Matrix.mul_smul, Matrix.smul_mul, gfun_smul,
      Matrix.mul_smul, Matrix.smul_mul, gfun_smul, Matrix.mul_one, unitary_star_mul hD, gfun_one]
    simp only [smul_comm Complex.I (_ : ℂ) (pauli _), Matrix.mul_smul, Matrix.smul_mul, gfun_smul]
    simp only [Complex.real_smul]
    ring
  rw [key]
  exact S.add_mem (S.add_mem (S.smul_mem _ (hmem 0)) (S.smul_mem _ (hmem 1))) (S.smul_mem _ (hmem 2))


/-- The two functions that a block adds beyond the span of the previous block. -/
def blockFa (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (x : ℝ) : ℂ :=
  (Real.cos x : ℂ) * gfun B ℓ (Complex.I • ((B ℓ)ᴴ * pauli 1 * B ℓ)) x -
    (Real.sin x : ℂ) * gfun B ℓ (Complex.I • ((B ℓ)ᴴ * pauli 2 * B ℓ)) x

def blockFb (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ) (x : ℝ) : ℂ :=
  (Real.sin x : ℂ) * gfun B ℓ (Complex.I • ((B ℓ)ᴴ * pauli 1 * B ℓ)) x +
    (Real.cos x : ℂ) * gfun B ℓ (Complex.I • ((B ℓ)ᴴ * pauli 2 * B ℓ)) x

theorem gfun_succ_herm (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℕ)
    (hB : B ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Yᴴ = Y) (x : ℝ) :
    gfun B (ℓ + 1) (Complex.I • Y) x =
      gfun B ℓ (Complex.I • ((B ℓ)ᴴ * ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0)) * B ℓ)) x +
      ((-(Y 0 1).im : ℝ) : ℂ) * blockFa B ℓ x + ((((Y 0 0).re - (Y 1 1).re) / 2 : ℝ) : ℂ) * blockFb B ℓ x := by
  rw [gfun_succ B ℓ hB, RXm_conj_herm hY]
  simp only [Matrix.mul_add, Matrix.add_mul, gfun_add, Matrix.mul_smul, Matrix.smul_mul, gfun_smul,
    blockFa, blockFb]
  push_cast
  ring

theorem herm_half_sum {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Yᴴ = Y) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (Bᴴ * ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0)) * B)ᴴ =
      Bᴴ * ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0)) * B := by
  have h : ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0))ᴴ = (1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, pauli_herm, hY]
    simp only [Matrix.mul_assoc]
    congr 1
    simp
  have := conj_herm (D := Bᴴ) h
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-- Span of the tangent-coefficient functions of blocks `0, …, ℓ`. -/
def serialSpanUpTo (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (ℓ : ℕ) : Submodule ℝ (ℝ → ℂ) :=
  Submodule.span ℝ {f | ∃ j : SIdx L tbl, (j.1 : ℕ) ≤ ℓ ∧ serialTangentFn L tbl G j = f}

instance serialSpanUpTo_fd (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (ℓ : ℕ) :
    FiniteDimensional ℝ (serialSpanUpTo L tbl G ℓ) := by
  apply FiniteDimensional.span_of_finite
  exact (Set.finite_range (serialTangentFn L tbl G)).subset (by rintro f ⟨j, -, rfl⟩; exact ⟨j, rfl⟩)

theorem serialSpanUpTo_zero_le (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    serialSpanUpTo L tbl G 0 ≤ Submodule.span ℝ (Set.range ![fun _ : ℝ => (1 : ℂ), fun _ => Complex.I]) := by
  apply Submodule.span_le.2
  rintro f ⟨⟨l, g, a⟩, hl, rfl⟩
  obtain ⟨D, -, hfun⟩ := serialTangentFn_eq_gfun L tbl G hG (l, g)
  have hl0 : (l : ℕ) = 0 := by simpa using hl
  set c := (Dᴴ * (Complex.I • pauli a) * D) 1 0
  have : serialTangentFn L tbl G (l, g, a) = c.re • (fun _ : ℝ => (1 : ℂ)) + c.im • (fun _ : ℝ => Complex.I) := by
    funext x
    rw [hfun a x, hl0, gfun_zero]
    show c = _
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
    exact (Complex.re_add_im c).symm
  rw [SetLike.mem_coe, this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem serialSpanUpTo_succ_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2)) (hG : InSU G)
    (ℓ : ℕ) :
    serialSpanUpTo L tbl G (ℓ + 1) ≤ serialSpanUpTo L tbl G ℓ ⊔
      Submodule.span ℝ (Set.range ![blockFa (serialBlk L tbl G) ℓ, blockFb (serialBlk L tbl G) ℓ]) := by
  apply Submodule.span_le.2
  rintro f ⟨⟨l, g, a⟩, hl, rfl⟩
  by_cases hlt : (l : ℕ) ≤ ℓ
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨(l, g, a), hlt, rfl⟩)
  have hl' : (l : ℕ) = ℓ + 1 := by simp at hl; omega
  obtain ⟨D, hD, hfun⟩ := serialTangentFn_eq_gfun L tbl G hG (l, g)
  set B := serialBlk L tbl G
  set Y := Dᴴ * pauli a * D with hYdef
  have hY : Yᴴ = Y := by
    have := conj_herm (D := Dᴴ) (pauli_herm a)
    rwa [Matrix.conjTranspose_conjTranspose] at this
  set ℓ' : Fin (L + 1) := ⟨ℓ, by omega⟩
  have hfirst := herm_mem_block_span L tbl htbl G hG ℓ' (herm_half_sum hY (B ℓ))
  have key : serialTangentFn L tbl G (l, g, a) =
      (fun x => gfun B ℓ' (Complex.I • ((B ℓ)ᴴ * ((1 / 2 : ℂ) • (Y + pauli 0 * Y * pauli 0)) * B ℓ)) x) +
      ((-(Y 0 1).im : ℝ) • blockFa B ℓ + (((Y 0 0).re - (Y 1 1).re) / 2 : ℝ) • blockFb B ℓ) := by
    funext x
    rw [hfun a x, hl']
    have e : Dᴴ * (Complex.I • pauli a) * D = Complex.I • Y := by
      rw [hYdef, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, gfun_succ_herm B ℓ (serialBlk_mem L tbl G hG ℓ) hY]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    rw [add_assoc]
  rw [SetLike.mem_coe, key]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · refine Submodule.span_mono ?_ hfirst
    rintro _ ⟨b, rfl⟩
    exact ⟨(ℓ', ⟨0, htbl⟩, b), le_rfl, rfl⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem serialSpanUpTo_finrank_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    ∀ ℓ, ℓ ≤ L → Module.finrank ℝ (serialSpanUpTo L tbl G ℓ) ≤ 2 * (ℓ + 1)
  | 0, _ => by
    haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range ![fun _ : ℝ => (1 : ℂ), fun _ => Complex.I])) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    refine (Submodule.finrank_mono (serialSpanUpTo_zero_le L tbl G hG)).trans ?_
    exact (finrank_range_le_card _).trans (by simp)
  | ℓ + 1, hℓ => by
    have ih := serialSpanUpTo_finrank_le L tbl htbl G hG ℓ (by omega)
    haveI h2fd : FiniteDimensional ℝ (Submodule.span ℝ
        (Set.range ![blockFa (serialBlk L tbl G) ℓ, blockFb (serialBlk L tbl G) ℓ])) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    haveI : FiniteDimensional ℝ (serialSpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ
        (Set.range ![blockFa (serialBlk L tbl G) ℓ, blockFb (serialBlk L tbl G) ℓ]) :
          Submodule ℝ (ℝ → ℂ)) :=
      Submodule.finiteDimensional_sup _ _
    refine (Submodule.finrank_mono (serialSpanUpTo_succ_le L tbl htbl G hG ℓ)).trans ?_
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    have h2 := finrank_range_le_card (R := ℝ) ![blockFa (serialBlk L tbl G) ℓ, blockFb (serialBlk L tbl G) ℓ]
    simp only [Fintype.card_fin] at h2
    change Module.finrank ℝ (Submodule.span ℝ
      (Set.range ![blockFa (serialBlk L tbl G) ℓ, blockFb (serialBlk L tbl G) ℓ])) ≤ 2 at h2
    omega

/-- **Proposition 4.4(i), upper bound.** The serial circuit offers at most 2(L+1) tangent directions, for every choice of
    gates. -/
theorem serial_tangent_rank_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    serialTangentRank L tbl G ≤ 2 * (L + 1) := by
  -- PROVIDED SOLUTION
  -- Notation: V_ℓ(x) = (block ℓ) RXm x (block ℓ−1) ⋯ RXm x (block 0), so the state is V_L(x) e₀.
  -- (1) Locality/form: for the coordinate j in block ℓ, ∂_jψ(x) = U(x) · i V_ℓ(x)ᴴ Y_j V_ℓ(x) e₀ with Y_j Hermitian
  --     (Y_j = the gate's Pauli word conjugated by the gates after it in the block; use `lieCurve_hasDerivAt`, the product
  --     rule through `blockProd` and `serialState`). With Tψ = −U e₁ (U ∈ SU(2), `Tpaper_eq_neg_T`-style computation),
  --     h_j(x) = −i ⟨e₁, V_ℓ(x)ᴴ Y_j V_ℓ(x) e₀⟩ up to a fixed sign.
  -- (2) Let T_ℓ = span of the functions of blocks 0..ℓ. Block 0: V_0 is constant, so its functions are constants in ℂ:
  --     dim T_0 ≤ 2.
  -- (3) Block ℓ ≥ 1: V_ℓ = B_ℓ RXm(x) V_{ℓ−1}. With K = B_ℓᴴ Y B_ℓ, RXm(x)ᴴ K RXm(x) = K₀ + e^{ix} K₊ + e^{−ix} K₊ᴴ
  --     where K₀ = P₊KP₊ + P₋KP₋ commutes with RXm, K₊ = P₊ K P₋, P± = (1 ± X)/2. The K₀ part gives
  --     −i⟨e₁, V_{ℓ−1}ᴴ K₀ V_{ℓ−1} e₀⟩, a real-linear combination of block-(ℓ−1) functions (the Pauli words of the last gate of
  --     block ℓ−1, conjugated, span all traceless Hermitian 2×2 matrices; the trace part contributes ⟨e₁, e₀⟩ = 0).
  --     The remainder depends real-linearly on K₊ ∈ P₊ ℂ^{2×2} P₋ ≅ ℂ (real dimension 2). Hence every block-ℓ function lies
  --     in T_{ℓ−1} + span of two fixed functions: dim T_ℓ ≤ dim T_{ℓ−1} + 2.
  -- (4) Induction: dim T_L ≤ 2 + 2L. Use `Submodule.span_union`, `Submodule.finrank_add_le_finrank_add_finrank` /
  --     `Submodule.finrank_sup_le`-type lemmas.
  refine le_trans ?_ (serialSpanUpTo_finrank_le L tbl htbl G hG L le_rfl)
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨j, Nat.lt_succ_iff.1 j.1.2, rfl⟩

set_option linter.unnecessarySeqFocus false in
theorem RXm_add (a b : ℝ) : RXm a * RXm b = RXm (a + b) := by
  rw [RXm_real, RXm_real, RXm_real]
  have hc : Real.cos ((a + b) / 2) = Real.cos (a / 2) * Real.cos (b / 2) - Real.sin (a / 2) * Real.sin (b / 2) := by
    rw [← Real.cos_add]; ring_nf
  have hs : Real.sin ((a + b) / 2) = Real.sin (a / 2) * Real.cos (b / 2) + Real.cos (a / 2) * Real.sin (b / 2) := by
    rw [← Real.sin_add]; ring_nf
  rw [hc, hs]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem blockProd_ones {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ t : ℕ, blockProd t (fun _ : Fin t => (1 : Matrix n n ℂ)) = 1
  | 0 => rfl
  | t + 1 => by simp only [blockProd]; rw [blockProd_ones t, Matrix.one_mul]

theorem blockProd_update_ones {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ (t : ℕ) (k : Fin t) (A : Matrix n n ℂ),
      blockProd t (Function.update (fun _ : Fin t => (1 : Matrix n n ℂ)) k A) = A
  | 0, k, _ => k.elim0
  | t + 1, k, A => by
    simp only [blockProd]
    by_cases hk : k = Fin.last t
    · subst hk
      rw [Function.update_self]
      have : (fun i : Fin t => Function.update (fun _ : Fin (t + 1) => (1 : Matrix n n ℂ)) (Fin.last t) A
          (Fin.castSucc i)) = fun _ => 1 := by
        funext i; exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
      rw [this, blockProd_ones, Matrix.mul_one]
    · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [Function.update_of_ne (Fin.castSucc_lt_last k').ne', Matrix.one_mul]
      have : (fun i : Fin t => Function.update (fun _ : Fin (t + 1) => (1 : Matrix n n ℂ)) (Fin.castSucc k') A
          (Fin.castSucc i)) = Function.update (fun _ : Fin t => (1 : Matrix n n ℂ)) k' A :=
        Function.update_comp_eq_of_injective (fun _ : Fin (t + 1) => (1 : Matrix n n ℂ))
          (Fin.castSucc_injective _) k' A
      rw [this, blockProd_update_ones t k' A]

theorem preState_ones (ℓ : ℕ) (x : ℝ) :
    preState (fun _ => 1) ℓ x = RXm (ℓ * x) *ᵥ ![1, 0] := by
  induction ℓ with
  | zero =>
    have h0 : RXm 0 = 1 := by ext i k; fin_cases i <;> fin_cases k <;> simp [RXm]
    simp only [preState, Nat.cast_zero, zero_mul, h0, Matrix.one_mulVec]
  | succ ℓ ih =>
    simp only [preState, ih, Matrix.mulVec_mulVec, Matrix.one_mul, RXm_add]
    congr 2; push_cast; ring

theorem gfun_ones (ℓ : ℕ) (a : Fin 3) (x : ℝ) :
    gfun (fun _ => 1) ℓ (Complex.I • pauli a) x =
      ![Complex.I, -((Real.cos (ℓ * x) : ℝ) : ℂ), -((Real.sin (ℓ * x) : ℝ) : ℂ)] a := by
  unfold gfun
  rw [preState_ones, RXm_real]
  have hc : Real.cos (ℓ * x) = Real.cos (ℓ * x / 2) ^ 2 - Real.sin (ℓ * x / 2) ^ 2 := by
    have := Real.cos_two_mul (ℓ * x / 2)
    rw [show 2 * (ℓ * x / 2) = ℓ * x by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (ℓ * x / 2)
  have hs : Real.sin (ℓ * x) = 2 * Real.sin (ℓ * x / 2) * Real.cos (ℓ * x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (ℓ * x / 2)
  rw [hc, hs]
  generalize Real.cos (ℓ * x / 2) = c at *
  generalize Real.sin (ℓ * x / 2) = s at *
  fin_cases a <;>
    simp [ip, T, pauli, pauli1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff, sq] <;>
    first | ring1 | linear_combination h1


theorem serialTangentFn_ones (L tbl : ℕ) (j : SIdx L tbl) (x : ℝ) :
    serialTangentFn L tbl (fun _ => 1) j x = gfun (fun _ => 1) j.1 (Complex.I • pauli j.2.2) x := by
  obtain ⟨l, g, a⟩ := j
  rw [serialTangentFn_eq]
  have hb : (fun ℓ : Fin (L + 1) => blockProd tbl (fun g' => perturb (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (l, g) (1 * (Complex.I • pauli a)) (ℓ, g'))) =
      Function.update (fun _ => 1) l (Complex.I • pauli a) := by
    funext ℓ
    by_cases hℓ : ℓ = l
    · subst hℓ
      rw [Function.update_self]
      refine Eq.trans ?_ (blockProd_update_ones tbl g (Complex.I • pauli a))
      congr 1
      funext g'
      by_cases hg : g' = g
      · subst hg; simp [perturb]
      · rw [Function.update_of_ne hg]
        simp only [perturb]
        rw [Function.update_of_ne (fun h => hg (congrArg Prod.snd h))]
    · rw [Function.update_of_ne hℓ]
      refine Eq.trans ?_ (blockProd_ones (n := Fin 2) tbl)
      congr 1
      funext g'
      simp only [perturb]
      rw [Function.update_of_ne (fun h => hℓ (congrArg Prod.fst h))]
  have h1 : (fun ℓ : Fin (L + 1) => blockProd tbl (fun g' => (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (ℓ, g'))) = Function.update (fun _ => 1) l 1 := by
    rw [Function.update_eq_self_iff.2 rfl]
    funext ℓ
    exact blockProd_ones tbl
  obtain ⟨Down, hDS, hDown⟩ := serialState_update_preState L (fun _ => 1) (fun _ => 1) (fun _ => rfl)
    (fun _ => one_mem _) l
  unfold gateState
  rw [hb, h1, hDown, hDown, gauge_invariance _ (hDS x), Matrix.one_mulVec]
  rfl

theorem ip_T_eq (u v : Fin 2 → ℂ) : ip (T u) v = -(u 1 * v 0) + u 0 * v 1 := by
  simp [ip, T]

theorem serialTangentFn_isCPoly (L tbl : ℕ) (j : SIdx L tbl) (x : ℝ) :
    IsCPoly (fun G : Gates L tbl (Fin 2) => serialTangentFn L tbl G j x) := by
  have hblk : ∀ (F : Gates L tbl (Fin 2) → Gates L tbl (Fin 2)),
      (∀ i a b, IsCPoly (fun G => F G i a b)) → ∀ a,
      IsCPoly (fun G => gateState L tbl (F G) x a) := by
    intro F hF a
    exact IsCPoly.serialState x L (fun G ℓ => blockProd tbl (fun g => F G (ℓ, g)))
      (fun ℓ => IsCPoly.blockProd tbl (fun G g => F G (ℓ, g)) (fun g => hF _)) a
  have hu := hblk id (fun i a b => IsCPoly.entry i a b)
  have hv := hblk _ (IsCPoly.perturb_mul (j.1, j.2.1) (Complex.I • pauli j.2.2))
  refine (((IsCPoly.const (-1)).mul ((hu 1).mul (hv 0))).add ((hu 0).mul (hv 1))).congr fun G => ?_
  rw [serialTangentFn_eq, ip_T_eq]
  simp only [id]
  ring


/-- The `2L+2` coordinates used for the serial lower bound: `X` and `Y` in block `0`, then `Y` and `Z` in each
    later block (first gate). -/
def serialWitIdx (L tbl : ℕ) (htbl : 1 ≤ tbl) : Option (Fin (2 * L + 1)) → SIdx L tbl
  | none => (0, ⟨0, htbl⟩, 0)
  | some r => (⟨((r : ℕ) + 1) / 2, by have := r.2; omega⟩, ⟨0, htbl⟩,
      if (r : ℕ) % 2 = 1 ∨ (r : ℕ) = 0 then 1 else 2)

/-- Samples of a function `ℝ → ℂ`: its imaginary part at `0` and its real part on the grid `eqGrid L 0`. -/
def serialSampler (L : ℕ) : (ℝ → ℂ) →ₗ[ℝ] (Option (Fin (2 * L + 1)) → ℝ) where
  toFun f o := o.elim (f 0).im (fun k => (f (eqGrid L 0 k)).re)
  map_add' f g := by funext o; cases o <;> simp
  map_smul' c f := by funext o; cases o <;> simp

theorem serial_witness_linInd (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    LinearIndependent ℝ (fun a => serialSampler L
      (serialTangentFn L tbl (fun _ => 1) (serialWitIdx L tbl htbl a))) := by
  set κ : Fin (2 * L + 1) → ℝ := fun r => if (r : ℕ) = 0 then -1 else if (r : ℕ) % 2 = 1 then -1 / 2 else 1 / 2
  have hκ : ∀ r, κ r ≠ 0 := by intro r; simp only [κ]; split_ifs <;> norm_num
  have hcos : ∀ (n : ℕ) (y : ℝ), (Complex.cos ((n : ℂ) * (y : ℂ))).re = Real.cos (n * y) := by
    intro n y; rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.cos_ofReal_re]
  have hsin : ∀ (n : ℕ) (y : ℝ), (Complex.sin ((n : ℂ) * (y : ℂ))).re = Real.sin (n * y) := by
    intro n y; rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.sin_ofReal_re]
  have hnone : ∀ o, serialSampler L (serialTangentFn L tbl (fun _ => 1) (serialWitIdx L tbl htbl none)) o =
      o.elim 1 (fun _ => 0) := by
    intro o
    cases o <;> simp [serialSampler, serialWitIdx, serialTangentFn_ones, gfun_ones]
  have hsome : ∀ r o, serialSampler L (serialTangentFn L tbl (fun _ => 1) (serialWitIdx L tbl htbl (some r))) o =
      o.elim 0 (fun k => κ r * designMatrix L (eqGrid L 0) k r) := by
    intro r o
    cases o with
    | none =>
      simp only [serialSampler, LinearMap.coe_mk, AddHom.coe_mk, Option.elim, serialTangentFn_ones, serialWitIdx]
      split_ifs <;> simp [gfun_ones]
    | some k =>
      simp only [serialSampler, LinearMap.coe_mk, AddHom.coe_mk, Option.elim, serialTangentFn_ones, serialWitIdx,
        designMatrix, κ]
      by_cases h0 : (r : ℕ) = 0
      · simp [h0, gfun_ones]
      · by_cases h1 : (r : ℕ) % 2 = 1
        · simp [h0, h1, gfun_ones, hcos]; ring
        · have he : ((r : ℕ) + 1) / 2 = (r : ℕ) / 2 := by omega
          simp [h0, h1, gfun_ones, he, hsin]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : ∀ o, ∑ a, g a * serialSampler L (serialTangentFn L tbl (fun _ => 1) (serialWitIdx L tbl htbl a)) o = 0 := by
    intro o
    have := congrFun hg o
    simpa [Finset.sum_apply] using this
  have hgn : g none = 0 := by
    have := hg' none
    simpa [Fintype.sum_option, hnone, hsome] using this
  have hv : designMatrix L (eqGrid L 0) *ᵥ (fun r => g (some r) * κ r) = 0 := by
    funext k
    have := hg' (some k)
    simp only [Fintype.sum_option, hnone, hsome, Option.elim, mul_zero, zero_add] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact (Finset.sum_congr rfl fun r _ => by ring).trans this
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero (design_det_ne_zero L 0) hv
  intro a
  cases a with
  | none => exact hgn
  | some r =>
    have := congrFun h0 r
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_right (hκ r)

/-- **Proposition 4.4(i), equality almost everywhere.** -/
theorem serial_tangent_rank_generic (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → Fin 2 → Fin 2 → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      serialTangentRank L tbl (fun i => Matrix.of (G i)) ≠ 2 * (L + 1)} = 0 := by
  -- PROVIDED SOLUTION
  -- By `serial_tangent_rank_le` the set is {rank < 2(L+1)} ∩ SU(2)^m. The functions are trigonometric polynomials of
  -- degree ≤ L (as in `gate_tangent_trig`), so their span has the same dimension as the span of their real and imaginary
  -- samples on the grid `eqGrid L 0` (2L+1 points; the design matrix there is invertible, `design_gram_eqGrid`).
  -- rank < k is the vanishing of the sum of squares of all k×k minors of the real sample matrix, a polynomial in
  -- `reIm G` (entries of products of gates, `RXm` at fixed points, and Pauli words; as in `serial_gramDet_poly`).
  -- Witness: all gates = 1 (∈ SU(2)). There, by the top-frequency argument, each block ℓ ≥ 1 adds two functions with
  -- independent coefficients at e^{±iℓx}, which no earlier block reaches (degree ≤ ℓ−1), and block 0 adds the two
  -- constants (real dimension 2): rank = 2(L+1). Concretely, with all gates = 1, RXm(x) = e^{−ix/2}P₊ + e^{ix/2}P₋ with
  -- P± = (1 ± X)/2, and the block-ℓ function of K₊ = |+⟩⟨−| m (m ∈ ℂ) has coefficient (up to a fixed nonzero factor) m at
  -- e^{iℓx} and conj m at e^{−iℓx}: two new real dimensions per block. Conclude with hμ applied to the minor polynomial
  -- (its value at the witness is nonzero).
  refine MeasureTheory.measure_mono_null ?_ (tangent_rank_generic_of_witness (serialTangentFn L tbl)
    (serialSampler L) (serialWitIdx L tbl htbl) (fun a k => ?_) (fun _ => 1) (fun _ => one_mem _)
    (serial_witness_linInd L tbl htbl) μ hμ)
  · rintro G ⟨hSU, hne⟩
    refine ⟨hSU, ?_⟩
    have := serial_tangent_rank_le L tbl htbl _ hSU
    unfold serialTangentRank at this hne
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  · cases k with
    | none => exact (serialTangentFn_isCPoly L tbl _ 0).2
    | some k => exact (serialTangentFn_isCPoly L tbl _ _).1

/-- Frame inner product at identity gates. -/
def ancWit (θ : ℝ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (r : Fin 3) : ℂ :=
  star (Matrix.kronecker (RXm θ) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ Pi.single (frameIdx r) 1) ⬝ᵥ
    ((Complex.I • P) *ᵥ (Matrix.kronecker (RXm θ) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ket00))

theorem ancWit_IX (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 0) (pauli1 1)) = ![Complex.I, 0, 0] := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff] <;>
    linarith

theorem ancWit_IY (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 0) (pauli1 2)) = ![-1, 0, 0] := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff] <;>
    linarith

theorem ancWit_XI (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 1) (pauli1 0)) = ![0, Complex.I, 0] := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff]
  linarith

theorem ancWit_YI (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 0)) = ![0, -((Real.cos θ : ℝ) : ℂ), 0] := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hc]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff, sq]
  linarith

theorem ancWit_XX (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 1) (pauli1 1)) = ![0, 0, Complex.I] := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff] <;>
    linarith

theorem ancWit_XY (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 1) (pauli1 2)) = ![0, 0, -1] := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff] <;>
    linarith

theorem ancWit_ZI (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 0)) = ![0, -((Real.sin θ : ℝ) : ℂ), 0] := by
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff]
  linarith

theorem ancWit_ZX (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 1)) = ![Complex.I * ((Real.cos θ : ℝ) : ℂ), 0, -((Real.sin θ : ℝ) : ℂ)] := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff, sq] <;>
    linarith

theorem ancWit_ZY (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 2)) = ![-((Real.cos θ : ℝ) : ℂ), 0, -(Complex.I * ((Real.sin θ : ℝ) : ℂ))] := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff, sq] <;>
    linarith

theorem ancWit_YX (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 1)) = ![-(Complex.I * ((Real.sin θ : ℝ) : ℂ)), 0, -((Real.cos θ : ℝ) : ℂ)] := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff, sq] <;>
    linarith

theorem ancWit_YY (θ : ℝ) :
    ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 2)) = ![((Real.sin θ : ℝ) : ℂ), 0, -(Complex.I * ((Real.cos θ : ℝ) : ℂ))] := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  unfold ancWit
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  funext r
  fin_cases r <;>
    simp [frameIdx, ket00, pauli1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff, sq] <;>
    linarith

theorem IsCPoly.ancillaUnitary {ι n : Type*} (x : ℝ) (L : ℕ) :
    ∀ (V : (ι → Matrix n n ℂ) → Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    (∀ ℓ a b, IsCPoly (fun G => V G ℓ a b)) →
      ∀ a b, IsCPoly (fun G => _root_.ancillaUnitary L (V G) x a b) := by
  induction L with
  | zero => intro V h a b; exact h 0 a b
  | succ L ih =>
    intro V h a b
    have h1 := ih (fun G ℓ => V G (Fin.castSucc ℓ)) (fun ℓ => h _)
    have h2 := IsCPoly.matMul (M := fun _ => Matrix.kronecker (RXm x) (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (fun a b => IsCPoly.const _) h1
    exact IsCPoly.matMul (M := fun G => V G (Fin.last (L + 1))) (h _) h2 a b

theorem ancillaTangentFn_isCPoly (L tbl : ℕ) (j : AIdx L tbl) (x : ℝ) (r : Fin 3) :
    IsCPoly (fun G : Gates L tbl (Fin 2 × Fin 2) => ancillaTangentFn L tbl G j x r) := by
  have hblk : ∀ (F : Gates L tbl (Fin 2 × Fin 2) → Gates L tbl (Fin 2 × Fin 2)),
      (∀ i a b, IsCPoly (fun G => F G i a b)) → ∀ ℓ a b,
      IsCPoly (fun G => ancillaBlocks L tbl (F G) ℓ a b) := by
    intro F hF ℓ a b
    exact IsCPoly.blockProd tbl (fun G g => F G (ℓ, g)) (fun g => hF _) a b
  have hU := IsCPoly.ancillaUnitary x L _ (hblk id (fun i a b => IsCPoly.entry i a b))
  have hv := IsCPoly.ancillaState x L _ (hblk _ (IsCPoly.perturb_mul (j.1, j.2.1) (Complex.I • pauliWord j.2.2)))
  refine (IsCPoly.sum Finset.univ fun a _ => (hU a (frameIdx r)).conj.mul (hv a)).congr fun G => ?_
  rw [ancillaTangentFn_eq]
  simp [dotProduct]

theorem blocks_perturb_ones {n : Type*} [Fintype n] [DecidableEq n] (L tbl : ℕ) (l : Fin (L + 1)) (g : Fin tbl)
    (A : Matrix n n ℂ) :
    (fun ℓ : Fin (L + 1) => blockProd tbl (fun g' => perturb (fun _ => (1 : Matrix n n ℂ)) (l, g) A (ℓ, g'))) =
      Function.update (fun _ => 1) l A := by
  funext ℓ
  by_cases hℓ : ℓ = l
  · subst hℓ
    rw [Function.update_self]
    refine Eq.trans ?_ (blockProd_update_ones tbl g A)
    congr 1
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [perturb]
    · rw [Function.update_of_ne hg]
      simp only [perturb]
      rw [Function.update_of_ne (fun h => hg (congrArg Prod.snd h))]
  · rw [Function.update_of_ne hℓ]
    refine Eq.trans ?_ (blockProd_ones (n := n) tbl)
    congr 1
    funext g'
    simp only [perturb]
    rw [Function.update_of_ne (fun h => hℓ (congrArg Prod.fst h))]

theorem RXm_zero' : RXm 0 = 1 := by ext i k; fin_cases i <;> fin_cases k <;> simp [RXm]

theorem kron_RXm_mul (a b : ℝ) :
    Matrix.kronecker (RXm a) (1 : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.kronecker (RXm b) 1 =
      Matrix.kronecker (RXm (a + b)) 1 := by
  rw [← RXm_add]
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem ancillaUnitary_ones (x : ℝ) :
    ∀ L : ℕ, ancillaUnitary L (fun _ => 1) x = Matrix.kronecker (RXm (L * x)) 1
  | 0 => by
    simp only [ancillaUnitary, Nat.cast_zero, zero_mul, RXm_zero']
    unfold Matrix.kronecker; rw [Matrix.one_kronecker_one]
  | L + 1 => by
    simp only [ancillaUnitary]
    rw [ancillaUnitary_ones x L, Matrix.one_mul, kron_RXm_mul]
    congr 2; push_cast; ring

theorem ancillaState_update_ones (x : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∀ (L : ℕ) (ℓ : Fin (L + 1)), ancillaState L (Function.update (fun _ => 1) ℓ M) x =
      Matrix.kronecker (RXm (((L : ℝ) - ℓ) * x)) 1 *ᵥ
        (M *ᵥ (Matrix.kronecker (RXm (ℓ * x)) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ket00))
  | 0, ℓ => by
    obtain rfl : ℓ = 0 := Fin.fin_one_eq_zero ℓ
    have h1 : Matrix.kronecker (RXm 0) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [RXm_zero']; unfold Matrix.kronecker; rw [Matrix.one_kronecker_one]
    simp only [ancillaState, Function.update_self, Fin.val_zero, Nat.cast_zero, sub_zero, zero_mul, h1,
      Matrix.one_mulVec]
  | L + 1, ℓ => by
    by_cases hℓ : ℓ = Fin.last (L + 1)
    · subst hℓ
      have hc : (fun i => Function.update (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
          (Fin.last (L + 1)) M (Fin.castSucc i)) = Function.update (fun _ => 1) 0 1 := by
        funext i
        rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne, Function.update_eq_self_iff.2 rfl]
      have h1 : Matrix.kronecker (RXm 0) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
        rw [RXm_zero']; unfold Matrix.kronecker; rw [Matrix.one_kronecker_one]
      simp only [ancillaState, Function.update_self]
      rw [hc, ancillaState_update_ones x 1 L 0]
      simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_mul, h1, Matrix.one_mulVec, sub_zero,
        Nat.cast_add, Nat.cast_one, sub_self]
      rw [Matrix.mulVec_mulVec _ (Matrix.kronecker (RXm x) 1), kron_RXm_mul]
      congr 4
      ring
    · obtain ⟨ℓ', rfl⟩ := Fin.exists_castSucc_eq.mpr hℓ
      have hc : (fun i => Function.update (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
          (Fin.castSucc ℓ') M (Fin.castSucc i)) = Function.update (fun _ => 1) ℓ' M :=
        Function.update_comp_eq_of_injective _ (Fin.castSucc_injective _) ℓ' M
      simp only [ancillaState]
      rw [Function.update_of_ne (Fin.castSucc_lt_last ℓ').ne', hc, ancillaState_update_ones x M L ℓ',
        Matrix.one_mulVec, Matrix.mulVec_mulVec _ (Matrix.kronecker (RXm x) 1), kron_RXm_mul, Fin.val_castSucc]
      congr 4
      push_cast; ring

theorem star_mulVec_dotProduct_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v w : ι → ℂ) : star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [show Uᴴ * U = 1 from (Matrix.mem_unitaryGroup_iff').1 hU, Matrix.one_mulVec]

theorem ancillaTangentFn_ones (L tbl : ℕ) (j : AIdx L tbl) (x : ℝ) (r : Fin 3) :
    ancillaTangentFn L tbl (fun _ => 1) j x r = ancWit (j.1 * x) (pauliWord j.2.2) r := by
  obtain ⟨l, g, p⟩ := j
  rw [ancillaTangentFn_eq]
  have hU : ancillaBlocks L tbl (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = fun _ => 1 := by
    funext ℓ; exact blockProd_ones tbl
  have hP : ancillaBlocks L tbl (perturb (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (l, g)
      (1 * (Complex.I • pauliWord p))) = Function.update (fun _ => 1) l (Complex.I • pauliWord p) := by
    rw [Matrix.one_mul]; exact blocks_perturb_ones L tbl l g _
  rw [hU, hP, ancillaState_update_ones, ancillaUnitary_ones]
  have hcol : (fun a => Matrix.kronecker (RXm (L * x)) (1 : Matrix (Fin 2) (Fin 2) ℂ) a (frameIdx r)) =
      Matrix.kronecker (RXm (((L : ℝ) - l) * x)) 1 *ᵥ
        (Matrix.kronecker (RXm (l * x)) (1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ Pi.single (frameIdx r) 1) := by
    rw [Matrix.mulVec_mulVec, kron_RXm_mul]
    funext a
    simp only [Matrix.mulVec, dotProduct_single, mul_one]
    congr 3; ring
  rw [hcol, star_mulVec_dotProduct_unitary _ (kron_one_mem_SU4 _ (RXm_mem_SU2 _)).1]
  rfl


/-- Pauli words used for the ancilla lower bound in block `0`: `IX, IY, XI, YI, XX, XY`. -/
def ancWords0 : Fin 6 → PWord :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 0), by decide⟩, ⟨(2, 0), by decide⟩,
    ⟨(1, 1), by decide⟩, ⟨(1, 2), by decide⟩]

/-- Pauli words used for the ancilla lower bound in blocks `ℓ ≥ 1`: `ZI, YI, ZX, ZY, YX, YY`. -/
def ancWords1 : Fin 6 → PWord :=
  ![⟨(3, 0), by decide⟩, ⟨(2, 0), by decide⟩, ⟨(3, 1), by decide⟩, ⟨(3, 2), by decide⟩,
    ⟨(2, 1), by decide⟩, ⟨(2, 2), by decide⟩]

/-- Values of the block-`0` witness functions (identity gates). -/
def ancGamma : Fin 6 → Fin 3 → ℂ :=
  ![![Complex.I, 0, 0], ![-1, 0, 0], ![0, Complex.I, 0], ![0, -1, 0], ![0, 0, Complex.I], ![0, 0, -1]]

/-- `cos(ℓx)` coefficients of the block-`ℓ` witness functions, `ℓ ≥ 1`. -/
def ancAlpha : Fin 6 → Fin 3 → ℂ :=
  ![![0, 0, 0], ![0, -1, 0], ![Complex.I, 0, 0], ![-1, 0, 0], ![0, 0, -1], ![0, 0, -Complex.I]]

/-- `sin(ℓx)` coefficients of the block-`ℓ` witness functions, `ℓ ≥ 1`. -/
def ancBeta : Fin 6 → Fin 3 → ℂ :=
  ![![0, -1, 0], ![0, 0, 0], ![0, 0, -1], ![0, 0, -Complex.I], ![-Complex.I, 0, 0], ![1, 0, 0]]

theorem ancWit_words0 (t : Fin 6) : ancWit 0 (pauliWord (ancWords0 t)) = ancGamma t := by
  fin_cases t
  · show ancWit 0 (Matrix.kronecker (pauli1 0) (pauli1 1)) = _
    rw [ancWit_IX]; funext r; fin_cases r <;> simp [ancGamma]
  · show ancWit 0 (Matrix.kronecker (pauli1 0) (pauli1 2)) = _
    rw [ancWit_IY]; funext r; fin_cases r <;> simp [ancGamma]
  · show ancWit 0 (Matrix.kronecker (pauli1 1) (pauli1 0)) = _
    rw [ancWit_XI]; funext r; fin_cases r <;> simp [ancGamma]
  · show ancWit 0 (Matrix.kronecker (pauli1 2) (pauli1 0)) = _
    rw [ancWit_YI]; funext r; fin_cases r <;> simp [ancGamma]
  · show ancWit 0 (Matrix.kronecker (pauli1 1) (pauli1 1)) = _
    rw [ancWit_XX]; funext r; fin_cases r <;> simp [ancGamma]
  · show ancWit 0 (Matrix.kronecker (pauli1 1) (pauli1 2)) = _
    rw [ancWit_XY]; funext r; fin_cases r <;> simp [ancGamma]

theorem ancWit_words1 (t : Fin 6) (θ : ℝ) :
    ancWit θ (pauliWord (ancWords1 t)) =
      fun r => ancAlpha t r * (Real.cos θ : ℂ) + ancBeta t r * (Real.sin θ : ℂ) := by
  fin_cases t
  · show ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 0)) = _
    rw [ancWit_ZI]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]
  · show ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 0)) = _
    rw [ancWit_YI]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]
  · show ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 1)) = _
    rw [ancWit_ZX]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]
  · show ancWit θ (Matrix.kronecker (pauli1 3) (pauli1 2)) = _
    rw [ancWit_ZY]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]
  · show ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 1)) = _
    rw [ancWit_YX]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]
  · show ancWit θ (Matrix.kronecker (pauli1 2) (pauli1 2)) = _
    rw [ancWit_YY]; funext r; fin_cases r <;> simp [ancAlpha, ancBeta]

/-- The `6(L+1)` coordinates used for the ancilla lower bound (first gate of each block). -/
def ancWitIdx (L tbl : ℕ) (htbl : 1 ≤ tbl) : Fin (L + 1) × Fin 6 → AIdx L tbl :=
  fun p => (p.1, ⟨0, htbl⟩, if (p.1 : ℕ) = 0 then ancWords0 p.2 else ancWords1 p.2)

theorem ancillaTangentFn_wit (L tbl : ℕ) (htbl : 1 ≤ tbl) (p : Fin (L + 1) × Fin 6) (x : ℝ) (r : Fin 3) :
    ancillaTangentFn L tbl (fun _ => 1) (ancWitIdx L tbl htbl p) x r =
      if (p.1 : ℕ) = 0 then ancGamma p.2 r
      else ancAlpha p.2 r * (Real.cos (p.1 * x) : ℂ) + ancBeta p.2 r * (Real.sin (p.1 * x) : ℂ) := by
  rw [ancillaTangentFn_ones]
  simp only [ancWitIdx]
  split_ifs with h
  · rw [h, Nat.cast_zero, zero_mul, ancWit_words0]
  · rw [ancWit_words1]

/-- Real or imaginary part. -/
def reimB (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

theorem reimB_add (b : Bool) (z w : ℂ) : reimB b (z + w) = reimB b z + reimB b w := by
  cases b <;> simp [reimB]

theorem reimB_ofReal_mul (b : Bool) (z : ℂ) (c : ℝ) : reimB b (z * (c : ℂ)) = reimB b z * c := by
  cases b <;> simp [reimB]

/-- Samples of a function `ℝ → ℂ³`: real and imaginary parts of each component on the grid `eqGrid L 0`. -/
def ancSampler (L : ℕ) : (ℝ → Fin 3 → ℂ) →ₗ[ℝ] (Fin 3 × Bool × Fin (2 * L + 1) → ℝ) where
  toFun f q := reimB q.2.1 (f (eqGrid L 0 q.2.2) q.1)
  map_add' f g := by funext q; obtain ⟨r, b, k⟩ := q; cases b <;> simp [reimB]
  map_smul' c f := by funext q; obtain ⟨r, b, k⟩ := q; cases b <;> simp [reimB]


/-- Design-matrix coefficients of the samples of the ancilla witness functions. -/
def ancCoef (L : ℕ) (p : Fin (L + 1) × Fin 6) (r : Fin 3) (b : Bool) : Fin (2 * L + 1) → ℝ :=
  if (p.1 : ℕ) = 0 then Pi.single ⟨0, by omega⟩ (reimB b (ancGamma p.2 r))
  else Pi.single ⟨2 * p.1 - 1, by have := p.1.2; omega⟩ (reimB b (ancAlpha p.2 r) / 2) +
    Pi.single ⟨2 * p.1, by have := p.1.2; omega⟩ (-reimB b (ancBeta p.2 r) / 2)

theorem mulVec_two_single {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) (a c : ℝ) (k : Fin m) :
    (M *ᵥ (Pi.single i a + Pi.single j c)) k = M k i * a + M k j * c := by
  simp [Matrix.mulVec, dotProduct_add, dotProduct_single]

theorem ancSample_eq (L tbl : ℕ) (htbl : 1 ≤ tbl) (p : Fin (L + 1) × Fin 6) (r : Fin 3) (b : Bool)
    (k : Fin (2 * L + 1)) :
    ancSampler L (ancillaTangentFn L tbl (fun _ => 1) (ancWitIdx L tbl htbl p)) (r, b, k) =
      (designMatrix L (eqGrid L 0) *ᵥ ancCoef L p r b) k := by
  have hf : ∀ x, ancillaTangentFn L tbl (fun _ => 1) (ancWitIdx L tbl htbl p) x r = _ :=
    fun x => ancillaTangentFn_wit L tbl htbl p x r
  simp only [ancSampler, LinearMap.coe_mk, AddHom.coe_mk, hf]
  unfold ancCoef
  split_ifs with h
  · simp [Matrix.mulVec, dotProduct_single, designMatrix]
  · have h1 : (2 * (p.1 : ℕ) - 1 + 1) / 2 = p.1 := by omega
    have h2 : (2 * (p.1 : ℕ) - 1) % 2 = 1 := by omega
    have h3 : 2 * (p.1 : ℕ) - 1 ≠ 0 := by omega
    have h4 : 2 * (p.1 : ℕ) / 2 = p.1 := by omega
    have h5 : 2 * (p.1 : ℕ) ≠ 0 := by omega
    have h6 : ¬ (2 * (p.1 : ℕ)) % 2 = 1 := by omega
    rw [mulVec_two_single]
    simp only [designMatrix, h1, h2, h3, h4, h5, h6, if_false, if_true, reimB_add, reimB_ofReal_mul]
    ring

theorem ancCoef_zero (L : ℕ) (p : Fin (L + 1) × Fin 6) (r : Fin 3) (b : Bool) :
    ancCoef L p r b ⟨0, by omega⟩ = if (p.1 : ℕ) = 0 then reimB b (ancGamma p.2 r) else 0 := by
  unfold ancCoef
  split_ifs with h
  · simp
  · simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem ancCoef_odd (L : ℕ) (p : Fin (L + 1) × Fin 6) (r : Fin 3) (b : Bool) (m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) :
    ancCoef L p r b ⟨2 * m - 1, by omega⟩ = if (p.1 : ℕ) = m then reimB b (ancAlpha p.2 r) / 2 else 0 := by
  unfold ancCoef
  split_ifs with h h'
  · omega
  · simp only [Pi.single_apply, Fin.ext_iff]; rw [if_neg (by omega)]
  · simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem ancCoef_even (L : ℕ) (p : Fin (L + 1) × Fin 6) (r : Fin 3) (b : Bool) (m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) :
    ancCoef L p r b ⟨2 * m, by omega⟩ = if (p.1 : ℕ) = m then -reimB b (ancBeta p.2 r) / 2 else 0 := by
  unfold ancCoef
  split_ifs with h h'
  · omega
  · simp only [Pi.single_apply, Fin.ext_iff]; rw [if_neg (by omega)]
  · simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    rw [if_neg (by omega), if_pos (by omega), zero_add]
  · simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem sum_select {L : ℕ} (g : Fin (L + 1) × Fin 6 → ℝ) (ℓ₀ : Fin (L + 1)) (F : Fin 6 → ℝ) :
    ∑ p, g p * (if (p.1 : ℕ) = ℓ₀ then F p.2 else 0) = ∑ t, g (ℓ₀, t) * F t := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ℓ₀]
  · simp
  · intro ℓ _ hne
    have : (ℓ : ℕ) ≠ ℓ₀ := fun h => hne (Fin.ext h)
    simp [this]
  · simp

theorem ancilla_witness_linInd (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    LinearIndependent ℝ (fun p => ancSampler L
      (ancillaTangentFn L tbl (fun _ => 1) (ancWitIdx L tbl htbl p))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcomp : ∀ r b, ∑ p, g p • ancCoef L p r b = 0 := by
    intro r b
    apply Matrix.eq_zero_of_mulVec_eq_zero (design_det_ne_zero L 0)
    funext k
    have := congrFun hg (r, b, k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ancSample_eq] at this
    have e : designMatrix L (eqGrid L 0) *ᵥ ∑ p, g p • ancCoef L p r b =
        ∑ p, g p • (designMatrix L (eqGrid L 0) *ᵥ ancCoef L p r b) := by
      simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [e]
    simpa [Finset.sum_apply] using this
  have hs : ∀ r b (s : Fin (2 * L + 1)), ∑ p, g p * ancCoef L p r b s = 0 := by
    intro r b s
    have := congrFun (hcomp r b) s
    simpa [Finset.sum_apply] using this
  rintro ⟨ℓ₀, t₀⟩
  by_cases h0 : (ℓ₀ : ℕ) = 0
  · have e : ∀ r b, ∑ t, g (ℓ₀, t) * reimB b (ancGamma t r) = 0 := by
      intro r b
      have := hs r b ⟨0, by omega⟩
      simp only [ancCoef_zero] at this
      rw [← h0] at this
      exact (sum_select g ℓ₀ (fun t => reimB b (ancGamma t r))).symm.trans this
    have e1 := e 0 false
    have e2 := e 0 true
    have e3 := e 1 false
    have e4 := e 1 true
    have e5 := e 2 false
    have e6 := e 2 true
    simp [Fin.sum_univ_six, ancGamma, reimB] at e1 e2 e3 e4 e5 e6
    fin_cases t₀ <;> simp <;> linarith
  · have hm1 : 1 ≤ (ℓ₀ : ℕ) := by omega
    have hm : (ℓ₀ : ℕ) ≤ L := by have := ℓ₀.2; omega
    have ea : ∀ r b, ∑ t, g (ℓ₀, t) * (reimB b (ancAlpha t r) / 2) = 0 := by
      intro r b
      have := hs r b ⟨2 * ℓ₀ - 1, by omega⟩
      simp only [ancCoef_odd L _ r b ℓ₀ hm1 hm] at this
      exact (sum_select g ℓ₀ (fun t => reimB b (ancAlpha t r) / 2)).symm.trans this
    have eb : ∀ r b, ∑ t, g (ℓ₀, t) * (-reimB b (ancBeta t r) / 2) = 0 := by
      intro r b
      have := hs r b ⟨2 * ℓ₀, by omega⟩
      simp only [ancCoef_even L _ r b ℓ₀ hm1 hm] at this
      exact (sum_select g ℓ₀ (fun t => -reimB b (ancBeta t r) / 2)).symm.trans this
    have e1 := eb 1 true
    have e2 := ea 1 true
    have e3 := ea 0 false
    have e4 := ea 0 true
    have e5 := eb 0 false
    have e6 := eb 0 true
    simp [Fin.sum_univ_six, ancAlpha, ancBeta, reimB] at e1 e2 e3 e4 e5 e6
    fin_cases t₀ <;> simp <;> linarith

/-- **Proposition 4.4(ii).** The ancilla circuit offers at least 6(L+1) tangent directions for almost every choice of
    gates. -/
theorem ancilla_tangent_rank_generic (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      ancillaTangentRank L tbl (fun i => Matrix.of (G i)) < 6 * (L + 1)} = 0 := by
  -- PROVIDED SOLUTION
  -- As for `serial_tangent_rank_generic`: rank < 6(L+1) is the vanishing of a polynomial in `reIm G` (sum of squares of
  -- 6(L+1)-minors of the real samples on 2L+1 equispaced points; the functions have degree ≤ L, cf. `ancillaModel_trig`).
  -- Witness: all gates = 1. With P± = |±⟩⟨±| ⊗ 1 on the encoded qubit, RXm(x) ⊗ 1 = e^{−ix/2}P₊ + e^{ix/2}P₋, and for
  -- block ℓ ≥ 1 the coefficient of its function at e^{iℓx} is i·π(P₊(|+⟩ ⊗ M u)) and at e^{−iℓx} is i·π(P₋(|−⟩ ⊗ Mᴴ w)),
  -- where K₊ = |+⟩⟨−| ⊗ M ranges over all M ∈ ℂ^{2×2} as the Pauli words of block ℓ vary, u = w = 2^{−1/2} e₀, and
  -- π takes the components r ≠ 00 in the frame U(x)|r⟩ (which at identity gates is RXm(x)^ℓ ⊗ 1 applied to |r⟩).
  -- The real-linear map M ↦ (M u, Mᴴ w) has rank 8 − 2 = 6 (kernel {M u = 0, Mᴴ w = 0}, real dimension 2), and π keeps
  -- these vectors (|±⟩ ⊗ z has the component |1⟩ ⊗ z). Functions of earlier blocks have degree ≤ ℓ−1, so block ℓ adds
  -- ≥ 6 dimensions; block 0 adds 6 (constant vectors ⟨r, Y e₀⟩, r ≠ 00, over Hermitian Y: all of ℂ³). Total ≥ 6(L+1).
  -- Conclude with `genericity` / hμ.
  refine MeasureTheory.measure_mono_null ?_ (tangent_rank_generic_of_witness (ancillaTangentFn L tbl)
    (ancSampler L) (ancWitIdx L tbl htbl) (fun a q => ?_) (fun _ => 1) (fun _ => one_mem _)
    (ancilla_witness_linInd L tbl htbl) μ hμ)
  · rintro G ⟨hSU, hlt⟩
    refine ⟨hSU, ?_⟩
    unfold ancillaTangentRank at hlt
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · obtain ⟨r, b, k⟩ := q
    cases b
    · exact (ancillaTangentFn_isCPoly L tbl (ancWitIdx L tbl htbl a) (eqGrid L 0 k) r).2.congr fun G => by simp [ancSampler, reimB]
    · exact (ancillaTangentFn_isCPoly L tbl (ancWitIdx L tbl htbl a) (eqGrid L 0 k) r).1.congr fun G => by simp [ancSampler, reimB]


/-! ## 22. Proposition 4.4(iii): the parallel circuit on two qubits

Both qubits encoded: one layer is `R_X(x) ⊗ R_X(x)`; with `L` layers, `E = 2L`. Same frame `U(x)|r⟩`, `r ≠ 00`, and the
same tangent-coefficient functions as for the ancilla circuit. -/

/-- Encoding layer of the two-qubit parallel circuit. -/
def par2Enc (x : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kronecker (RXm x) (RXm x)

/-- State `W_L S(x) W_{L−1} ⋯ S(x) W_0 |00⟩` with `S(x) = R_X(x) ⊗ R_X(x)`. -/
def parallel2State : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) → ℝ → Fin 2 × Fin 2 → ℂ
  | 0, W, _ => W 0 *ᵥ ket00
  | L + 1, W, x => W (Fin.last (L + 1)) *ᵥ (par2Enc x *ᵥ parallel2State L (fun i => W (Fin.castSucc i)) x)

/-- The same circuit as a matrix. -/
def parallel2Unitary : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) → ℝ →
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | 0, W, _ => W 0
  | L + 1, W, x => W (Fin.last (L + 1)) * (par2Enc x * parallel2Unitary L (fun i => W (Fin.castSucc i)) x)

/-- Tangent-coefficient functions: h_j(x) = (⟨U(x)|r⟩, ∂_jψ(x)⟩)_{r ≠ 00}. -/
def parallel2TangentFn (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) : ℝ → Fin 3 → ℂ :=
  fun x r => dotProduct (star (fun a => parallel2Unitary L (ancillaBlocks L tbl G) x a (frameIdx r)))
    (deriv (fun s => parallel2State L (ancillaBlocks L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s))) x) 0)

/-- Real dimension of their span. -/
def parallel2TangentRank (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (parallel2TangentFn L tbl G)))

/-! ### Helper lemmas for Proposition 4.4(iii) -/

local notation "M4" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Kronecker product of two one-qubit Pauli matrices. -/
def pw2 (a b : Fin 4) : M4 := Matrix.kronecker (pauli1 a) (pauli1 b)

theorem RXm_unitary (x : ℝ) : (RXm x)ᴴ * RXm x = 1 :=
  (Matrix.mem_unitaryGroup_iff').1 (RXm_mem_SU2 x).1

theorem par2Enc_mem (x : ℝ) : par2Enc x ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show (Matrix.kroneckerMap (· * ·) (RXm x) (RXm x))ᴴ * Matrix.kroneckerMap (· * ·) (RXm x) (RXm x) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, RXm_unitary, Matrix.one_kronecker_one]

theorem par2Enc_add (a b : ℝ) : par2Enc a * par2Enc b = par2Enc (a + b) := by
  show Matrix.kroneckerMap (· * ·) (RXm a) (RXm a) * Matrix.kroneckerMap (· * ·) (RXm b) (RXm b) =
    Matrix.kroneckerMap (· * ·) (RXm (a + b)) (RXm (a + b))
  rw [← Matrix.mul_kronecker_mul, RXm_add]

theorem par2Enc_zero : par2Enc 0 = 1 := by
  show Matrix.kroneckerMap (· * ·) (RXm 0) (RXm 0) = 1
  rw [RXm_zero', Matrix.one_kronecker_one]

theorem par2Enc_conj_pw2 (θ : ℝ) (a b : Fin 4) :
    (par2Enc θ)ᴴ * pw2 a b * par2Enc θ =
      Matrix.kronecker ((RXm θ)ᴴ * pauli1 a * RXm θ) ((RXm θ)ᴴ * pauli1 b * RXm θ) := by
  show (Matrix.kroneckerMap (· * ·) (RXm θ) (RXm θ))ᴴ * Matrix.kroneckerMap (· * ·) (pauli1 a) (pauli1 b) *
    Matrix.kroneckerMap (· * ·) (RXm θ) (RXm θ) = _
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

theorem par2Enc_comm (x : ℝ) (Q : M4) (h : par2Enc x * Q = Q * par2Enc x) :
    (par2Enc x)ᴴ * Q * par2Enc x = Q := by
  have hu : (par2Enc x)ᴴ * par2Enc x = 1 := (Matrix.mem_unitaryGroup_iff').1 (par2Enc_mem x)
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem par2Enc_comm_check (x : ℝ) (Q : M4)
    (h : ∀ c s : ℂ, c ^ 2 + s ^ 2 = 1 →
      Matrix.kronecker !![c, -Complex.I * s; -Complex.I * s, c] !![c, -Complex.I * s; -Complex.I * s, c] * Q =
      Q * Matrix.kronecker !![c, -Complex.I * s; -Complex.I * s, c] !![c, -Complex.I * s; -Complex.I * s, c]) :
    (par2Enc x)ᴴ * Q * par2Enc x = Q := by
  apply par2Enc_comm
  have h1 := Real.cos_sq_add_sin_sq (x / 2)
  have := h (Real.cos (x / 2)) (Real.sin (x / 2)) (by exact_mod_cast h1)
  unfold par2Enc
  rw [RXm_real]
  exact this

theorem comm_YYZZ (x : ℝ) : (par2Enc x)ᴴ * (pw2 2 2 + pw2 3 3) * par2Enc x = pw2 2 2 + pw2 3 3 := by
  apply par2Enc_comm_check
  intro c s h
  ext ⟨a, b⟩ ⟨d, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [pw2, pauli1, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker,
      Matrix.kroneckerMap_apply] <;> ring_nf


theorem rx_conj_I (θ : ℝ) : (RXm θ)ᴴ * pauli1 0 * RXm θ = pauli1 0 := by
  simp only [pauli1, Matrix.cons_val_zero, Matrix.mul_one, RXm_unitary]

theorem rx_conj_X (θ : ℝ) : (RXm θ)ᴴ * pauli1 1 * RXm θ = pauli1 1 := by
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  rw [RXm_real]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, Complex.ext_iff] <;>
    nlinarith

theorem rx_conj_Y (θ : ℝ) : (RXm θ)ᴴ * pauli1 2 * RXm θ =
    ((Real.cos θ : ℝ) : ℂ) • pauli1 2 - ((Real.sin θ : ℝ) : ℂ) • pauli1 3 := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, Complex.ext_iff, sq] <;>
    ring_nf

theorem rx_conj_Z (θ : ℝ) : (RXm θ)ᴴ * pauli1 3 * RXm θ =
    ((Real.cos θ : ℝ) : ℂ) • pauli1 3 + ((Real.sin θ : ℝ) : ℂ) • pauli1 2 := by
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linear_combination this + Real.cos_sq_add_sin_sq (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.cos_sq_add_sin_sq (θ / 2)
  rw [RXm_real, hc, hs]
  generalize Real.cos (θ / 2) = c at *
  generalize Real.sin (θ / 2) = s at *
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, Complex.ext_iff, sq] <;>
    ring_nf

theorem comm_ZYYZ (x : ℝ) : (par2Enc x)ᴴ * (pw2 3 2 - pw2 2 3) * par2Enc x = pw2 3 2 - pw2 2 3 := by
  apply par2Enc_comm_check
  intro c s h
  ext ⟨a, b⟩ ⟨d, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [pw2, pauli1, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kronecker,
      Matrix.kroneckerMap_apply] <;> ring_nf

theorem comm_low (x : ℝ) (a b : Fin 4) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (par2Enc x)ᴴ * pw2 a b * par2Enc x = pw2 a b := by
  rw [par2Enc_conj_pw2]
  have h : ∀ k : Fin 4, k = 0 ∨ k = 1 → (RXm x)ᴴ * pauli1 k * RXm x = pauli1 k := by
    rintro k (rfl | rfl)
    · exact rx_conj_I x
    · exact rx_conj_X x
  rw [h a ha, h b hb]
  rfl


/-- Circuit prefix before block `k` (ℕ-indexed blocks `B`): `S(x) B_{k−1} ⋯ S(x) B_0`. -/
def par2Pre (B : ℕ → M4) : ℕ → ℝ → M4
  | 0, _ => 1
  | k + 1, x => par2Enc x * (B k * par2Pre B k x)

theorem parallel2_eq_pre : ∀ (L : ℕ) (W : Fin (L + 1) → M4) (B : ℕ → M4), (∀ k : Fin (L + 1), B k = W k) →
    ∀ x, parallel2State L W x = W (Fin.last L) *ᵥ (par2Pre B L x *ᵥ ket00) ∧
      parallel2Unitary L W x = W (Fin.last L) * par2Pre B L x
  | 0, W, B, _, x => by simp [parallel2State, parallel2Unitary, par2Pre]
  | L + 1, W, B, hB, x => by
    obtain ⟨h1, h2⟩ := parallel2_eq_pre L (fun i => W (Fin.castSucc i)) B (fun k => hB k.castSucc) x
    have hL : B L = W (Fin.last L).castSucc := by rw [← hB]; simp
    simp only [parallel2State, parallel2Unitary, par2Pre, h1, h2, hL, Matrix.mulVec_mulVec]
    constructor <;> trivial

theorem parallel2_update : ∀ (L : ℕ) (W : Fin (L + 1) → M4) (B : ℕ → M4), (∀ k : Fin (L + 1), B k = W k) →
    ∀ ℓ : Fin (L + 1), ∃ Down : ℝ → M4,
      ((∀ i, W i ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) →
        ∀ x, Down x ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      ∀ M x, parallel2State L (Function.update W ℓ M) x = Down x *ᵥ (M *ᵥ (par2Pre B ℓ x *ᵥ ket00)) ∧
        parallel2Unitary L (Function.update W ℓ M) x = Down x * (M * par2Pre B ℓ x)
  | 0, W, B, _, ℓ => by
    obtain rfl : ℓ = 0 := Fin.fin_one_eq_zero ℓ
    refine ⟨fun _ => 1, fun _ _ => one_mem _, fun M x => ?_⟩
    simp [parallel2State, parallel2Unitary, par2Pre]
  | L + 1, W, B, hB, ℓ => by
    by_cases hℓ : ℓ = Fin.last (L + 1)
    · subst hℓ
      refine ⟨fun _ => 1, fun _ _ => one_mem _, fun M x => ?_⟩
      have hc : (fun i => Function.update W (Fin.last (L + 1)) M (Fin.castSucc i)) =
          fun i => W (Fin.castSucc i) := by
        funext i; exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
      obtain ⟨h1, h2⟩ := parallel2_eq_pre L (fun i => W (Fin.castSucc i)) B (fun k => hB k.castSucc) x
      have hL : B L = W (Fin.last L).castSucc := by rw [← hB]; simp
      simp only [parallel2State, parallel2Unitary, Function.update_self, hc, h1, h2, Fin.val_last, par2Pre, hL,
        Matrix.one_mul, Matrix.mulVec_mulVec]
      constructor <;> trivial
    · obtain ⟨ℓ', rfl⟩ := Fin.exists_castSucc_eq.mpr hℓ
      obtain ⟨Down, hDS, hDown⟩ := parallel2_update L (fun i => W (Fin.castSucc i)) B
        (fun k => hB k.castSucc) ℓ'
      refine ⟨fun x => W (Fin.last (L + 1)) * (par2Enc x * Down x),
        fun hW x => mul_mem (hW _) (mul_mem (par2Enc_mem x) (hDS (fun i => hW _) x)), fun M x => ?_⟩
      have hc : (fun i => Function.update W (Fin.castSucc ℓ') M (Fin.castSucc i)) =
          Function.update (fun i => W (Fin.castSucc i)) ℓ' M :=
        Function.update_comp_eq_of_injective W (Fin.castSucc_injective _) ℓ' M
      obtain ⟨h1, h2⟩ := hDown M x
      simp only [parallel2State, parallel2Unitary]
      rw [Function.update_of_ne (Fin.castSucc_lt_last ℓ').ne', hc, h1, h2]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Fin.val_castSucc]
      constructor <;> trivial

/-- Frame inner products `(⟨P|r⟩, M P|00⟩)_{r ≠ 00}` after the prefix `P = par2Pre B ℓ x`. -/
def par2Q (B : ℕ → M4) (ℓ : ℕ) (M : M4) (x : ℝ) : Fin 3 → ℂ :=
  fun r => ((par2Pre B ℓ x)ᴴ * M * par2Pre B ℓ x) (frameIdx r) (0, 0)

theorem frame_dot (V P K : M4) (hV : V ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) (a : Fin 2 × Fin 2) :
    star ((V * P) *ᵥ Pi.single a 1) ⬝ᵥ (V *ᵥ (K *ᵥ (P *ᵥ ket00))) = (Pᴴ * K * P) a (0, 0) := by
  rw [← Matrix.mulVec_mulVec, star_mulVec_dotProduct_unitary _ hV, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, ket00, Pi.single_apply, Matrix.mul_assoc]

/-- ℕ-indexed blocks of the parallel circuit (identity past the last block). -/
def par2Blk (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (k : ℕ) : M4 :=
  if h : k < L + 1 then blockProd tbl (fun g => G (⟨k, h⟩, g)) else 1

theorem par2Blk_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (k : Fin (L + 1)) :
    par2Blk L tbl G k = ancillaBlocks L tbl G k := by
  simp [par2Blk, ancillaBlocks, k.2]

theorem par2Blk_mem (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) (k : ℕ) :
    par2Blk L tbl G k ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  unfold par2Blk
  split_ifs
  · exact (blockProd_mem _ tbl _ fun g => hG _).1
  · exact one_mem _

theorem parallel2TangentFn_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) (x : ℝ) (r : Fin 3) :
    parallel2TangentFn L tbl G j x r =
      star (fun a => parallel2Unitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
        parallel2State L (ancillaBlocks L tbl
          (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x := by
  unfold parallel2TangentFn
  congr 1
  obtain ⟨U, D, -, -, hUD⟩ := gate_blocks_update G (j.1, j.2.1)
  obtain ⟨Down, -, hDown⟩ := parallel2_update L (ancillaBlocks L tbl G) (par2Blk L tbl G)
    (par2Blk_eq L tbl G) j.1
  have hb : ∀ A, ancillaBlocks L tbl (perturb G (j.1, j.2.1) A) =
      Function.update (ancillaBlocks L tbl G) j.1 (U * A * D) := fun A => hUD A
  have e0 : ancillaBlocks L tbl G = ancillaBlocks L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1))) := by
    rw [perturb_self]
  have e : (fun s => parallel2State L (ancillaBlocks L tbl
      (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s))) x) =
      fun s : ℝ => (Real.cos s : ℂ) • parallel2State L (ancillaBlocks L tbl G) x + (Real.sin s : ℂ) •
        parallel2State L (ancillaBlocks L tbl
          (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x := by
    funext s
    rw [e0, hb, hb, hb, (hDown _ x).1, (hDown _ x).1, (hDown _ x).1, lieCurve_eq_comb]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [e]
  exact (cos_sin_comb_hasDerivAt _ _).deriv

theorem col_eq_mulVec (U : M4) (a : Fin 2 × Fin 2) : (fun b => U b a) = U *ᵥ Pi.single a 1 := by
  funext b
  simp [Matrix.mulVec, dotProduct_single]

theorem par2TangentFn_eq_Q (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (l : Fin (L + 1)) (g : Fin tbl) :
    ∃ D ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ, ∀ p x,
      parallel2TangentFn L tbl G (l, g, p) x =
        par2Q (par2Blk L tbl G) l (Dᴴ * (Complex.I • pauliWord p) * D) x := by
  obtain ⟨U, D, -, hD, hUD⟩ := gate_blocks_update G (l, g)
  have hDu := (hD hG).1
  have hDD : D * Dᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hDu
  obtain ⟨Down, hDS, hDown⟩ := parallel2_update L (ancillaBlocks L tbl G) (par2Blk L tbl G)
    (par2Blk_eq L tbl G) l
  have hWu : ∀ ℓ, ancillaBlocks L tbl G ℓ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    fun ℓ => (blockProd_mem _ tbl _ fun g => hG _).1
  have hWl : ancillaBlocks L tbl G l = U * G (l, g) * D := by
    have := congrFun (hUD (G (l, g))) l
    rw [perturb_self] at this
    simpa using this
  refine ⟨D, hDu, fun p x => ?_⟩
  funext r
  rw [parallel2TangentFn_eq]
  have e1 : parallel2Unitary L (ancillaBlocks L tbl G) x =
      (Down x * ancillaBlocks L tbl G l) * par2Pre (par2Blk L tbl G) l x := by
    conv_lhs => rw [← Function.update_eq_self l (ancillaBlocks L tbl G)]
    rw [(hDown _ x).2, Matrix.mul_assoc]
  have e2 : parallel2State L (ancillaBlocks L tbl
      (perturb G (l, g) (G (l, g) * (Complex.I • pauliWord p)))) x =
      (Down x * ancillaBlocks L tbl G l) *ᵥ ((Dᴴ * (Complex.I • pauliWord p) * D) *ᵥ
        (par2Pre (par2Blk L tbl G) l x *ᵥ ket00)) := by
    have hcalc : U * (G (l, g) * (Complex.I • pauliWord p)) * D =
        ancillaBlocks L tbl G l * (Dᴴ * (Complex.I • pauliWord p) * D) := by
      rw [hWl]
      calc U * (G (l, g) * (Complex.I • pauliWord p)) * D
          = U * G (l, g) * (D * Dᴴ) * (Complex.I • pauliWord p) * D := by
            rw [hDD]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [show ancillaBlocks L tbl (perturb G (l, g) (G (l, g) * (Complex.I • pauliWord p))) =
      Function.update (ancillaBlocks L tbl G) l (U * (G (l, g) * (Complex.I • pauliWord p)) * D) from hUD _,
      (hDown _ x).1, hcalc]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [col_eq_mulVec, e1, e2, frame_dot _ _ _ (mul_mem (hDS hWu x) (hWu _))]
  rfl


theorem pw2_herm (a b : Fin 4) : (pw2 a b)ᴴ = pw2 a b := by
  show (Matrix.kroneckerMap (· * ·) (pauli1 a) (pauli1 b))ᴴ = _
  rw [Matrix.conjTranspose_kronecker, pauli1_herm, pauli1_herm]
  rfl

theorem pw2_zero : pw2 0 0 = 1 := by
  show Matrix.kroneckerMap (· * ·) (pauli1 0) (pauli1 0) = 1
  simp only [pauli1, Matrix.cons_val_zero]
  exact Matrix.one_kronecker_one

theorem trace_pw2_herm_im (W : M4) (hW : Wᴴ = W) (a b : Fin 4) : ((pw2 a b * W).trace).im = 0 := by
  have hreal : (starRingEnd ℂ) ((pw2 a b * W).trace) = (pw2 a b * W).trace := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hW, pw2_herm,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp hreal

theorem herm_decomp4 (W : M4) (hW : Wᴴ = W) :
    Complex.I • W = ∑ q : Fin 4 × Fin 4,
      ((((pw2 q.1 q.2 * W).trace / 4).re : ℝ) : ℂ) • (Complex.I • pw2 q.1 q.2) := by
  conv_lhs => rw [pauli2_complete W]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ((((pw2 q.1 q.2 * W).trace / 4).re : ℝ) : ℂ) = (pw2 q.1 q.2 * W).trace / 4 := by
    apply Complex.ext
    · simp
    · simp [trace_pw2_herm_im W hW]
  rw [h, smul_comm]
  rfl

theorem conj_herm4 {D Z : M4} (hZ : Zᴴ = Z) : (Dᴴ * Z * D)ᴴ = Dᴴ * Z * D := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hZ,
    Matrix.mul_assoc]

theorem par2Q_add (B : ℕ → M4) (ℓ : ℕ) (M N : M4) (x : ℝ) :
    par2Q B ℓ (M + N) x = par2Q B ℓ M x + par2Q B ℓ N x := by
  funext r; simp [par2Q, Matrix.mul_add, Matrix.add_mul]

theorem par2Q_sub (B : ℕ → M4) (ℓ : ℕ) (M N : M4) (x : ℝ) :
    par2Q B ℓ (M - N) x = par2Q B ℓ M x - par2Q B ℓ N x := by
  funext r; simp [par2Q, Matrix.mul_sub, Matrix.sub_mul]

theorem par2Q_sum_fn (B : ℕ → M4) (ℓ : ℕ) (a : Fin 4 × Fin 4 → ℝ) (M : Fin 4 × Fin 4 → M4) :
    (fun x => par2Q B ℓ (∑ q, (a q : ℂ) • M q) x) = ∑ q, a q • (fun x => par2Q B ℓ (M q) x) := by
  funext x r
  simp [par2Q, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Finset.sum_apply, Complex.real_smul]

theorem par2Pre_mem (B : ℕ → M4) (hB : ∀ k, B k ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) :
    ∀ ℓ x, par2Pre B ℓ x ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ
  | 0, _ => one_mem _
  | ℓ + 1, x => mul_mem (par2Enc_mem x) (mul_mem (hB ℓ) (par2Pre_mem B hB ℓ x))

theorem par2Q_I (B : ℕ → M4) (hB : ∀ k, B k ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) (ℓ : ℕ) (x : ℝ) :
    par2Q B ℓ (Complex.I • 1) x = 0 := by
  funext r
  have hu : (par2Pre B ℓ x)ᴴ * par2Pre B ℓ x = 1 := (Matrix.mem_unitaryGroup_iff').1 (par2Pre_mem B hB ℓ x)
  simp only [par2Q, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hu]
  fin_cases r <;> simp [frameIdx]

theorem par2Q_succ (B : ℕ → M4) (ℓ : ℕ) (M : M4) (x : ℝ) :
    par2Q B (ℓ + 1) M x = par2Q B ℓ ((B ℓ)ᴴ * ((par2Enc x)ᴴ * M * par2Enc x) * B ℓ) x := by
  funext r
  simp only [par2Q, par2Pre, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem par2Q_zero (B : ℕ → M4) (M : M4) (x : ℝ) : par2Q B 0 M x = fun r => M (frameIdx r) (0, 0) := by
  funext r; simp [par2Q, par2Pre]

/-- For Hermitian `Z`, `x ↦ π(P_ℓ(x)ᴴ iZ P_ℓ(x) |00⟩)` is a real combination of the tangent-coefficient functions of the
    first gate of block `ℓ`. -/
theorem par2_herm_mem (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (ℓ : Fin (L + 1)) {Z : M4} (hZ : Zᴴ = Z) :
    (fun x => par2Q (par2Blk L tbl G) ℓ (Complex.I • Z) x) ∈
      Submodule.span ℝ (Set.range fun p : PWord => parallel2TangentFn L tbl G (ℓ, ⟨0, htbl⟩, p)) := by
  obtain ⟨D, hD, hfun⟩ := par2TangentFn_eq_Q L tbl G hG ℓ ⟨0, htbl⟩
  have hDD : D * Dᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hD
  have hDD' : Dᴴ * D = 1 := (Matrix.mem_unitaryGroup_iff').1 hD
  set W := Dᴴᴴ * Z * Dᴴ with hWdef
  have hW : Wᴴ = W := conj_herm4 hZ
  have hZW : Complex.I • Z = Dᴴ * (Complex.I • W) * D := by
    simp only [hWdef, Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc, hDD', Matrix.one_mul]
    rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
  have key : (fun x => par2Q (par2Blk L tbl G) ℓ (Complex.I • Z) x) =
      ∑ q : Fin 4 × Fin 4, (((pw2 q.1 q.2 * W).trace / 4).re) •
        (fun x => par2Q (par2Blk L tbl G) ℓ (Dᴴ * (Complex.I • pw2 q.1 q.2) * D) x) := by
    rw [hZW, herm_decomp4 W hW, Matrix.mul_sum, Matrix.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    exact par2Q_sum_fn _ _ _ _
  rw [key]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
  by_cases hq : q = (0, 0)
  · subst hq
    have h1 : Dᴴ * (Complex.I • pw2 (0, 0).1 (0, 0).2) * D = Complex.I • 1 := by
      rw [show ((0 : Fin 4), (0 : Fin 4)).1 = 0 from rfl, show ((0 : Fin 4), (0 : Fin 4)).2 = 0 from rfl,
        pw2_zero, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD']
    have h2 : (fun x => par2Q (par2Blk L tbl G) ℓ (Dᴴ * (Complex.I • pw2 (0, 0).1 (0, 0).2) * D) x) = 0 := by
      funext x
      rw [h1, par2Q_I _ (par2Blk_mem L tbl G hG)]
      rfl
    rw [h2]
    exact Submodule.zero_mem _
  · have : (fun x => par2Q (par2Blk L tbl G) ℓ (Dᴴ * (Complex.I • pw2 q.1 q.2) * D) x) =
        parallel2TangentFn L tbl G (ℓ, ⟨0, htbl⟩, ⟨q, hq⟩) := by
      funext x; rw [hfun]; rfl
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- Span of the tangent-coefficient functions of blocks `0, …, ℓ`. -/
def par2SpanUpTo (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (ℓ : ℕ) : Submodule ℝ (ℝ → Fin 3 → ℂ) :=
  Submodule.span ℝ {f | ∃ j : AIdx L tbl, (j.1 : ℕ) ≤ ℓ ∧ parallel2TangentFn L tbl G j = f}

instance par2SpanUpTo_fd (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (ℓ : ℕ) :
    FiniteDimensional ℝ (par2SpanUpTo L tbl G ℓ) := by
  apply FiniteDimensional.span_of_finite
  exact (Set.finite_range (parallel2TangentFn L tbl G)).subset (by rintro f ⟨j, -, rfl⟩; exact ⟨j, rfl⟩)

/-- The constant functions `ℝ → ℂ³`. -/
def par2Const : (Fin 3 → ℂ) →ₗ[ℝ] (ℝ → Fin 3 → ℂ) := LinearMap.pi (fun _ : ℝ => LinearMap.id)

theorem par2SpanUpTo_zero_le (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    par2SpanUpTo L tbl G 0 ≤ LinearMap.range par2Const := by
  apply Submodule.span_le.2
  rintro f ⟨⟨l, g, p⟩, hl, rfl⟩
  obtain ⟨D, -, hfun⟩ := par2TangentFn_eq_Q L tbl G hG l g
  have hl0 : (l : ℕ) = 0 := by simpa using hl
  refine ⟨fun r => (Dᴴ * (Complex.I • pauliWord p) * D) (frameIdx r) (0, 0), ?_⟩
  funext x
  rw [hfun p x, hl0, par2Q_zero]
  rfl

theorem par2Const_finrank : Module.finrank ℝ (Fin 3 → ℂ) = 6 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]


/-- The ten Pauli words whose functions a block adds beyond the previous blocks:
    `IY, IZ, XY, XZ, YI, YX, ZI, ZX, YY, YZ`. -/
def par2New : Fin 10 → Fin 4 × Fin 4 :=
  ![(0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (3, 0), (3, 1), (2, 2), (2, 3)]

/-- The corresponding functions after the prefix of block `ℓ + 1`. -/
def par2NewFn (B : ℕ → M4) (ℓ : ℕ) (k : Fin 10) : ℝ → Fin 3 → ℂ :=
  fun x => par2Q B (ℓ + 1) (Complex.I • pw2 (par2New k).1 (par2New k).2) x

theorem par2_comm_mem (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (ℓ : ℕ) (hℓ : ℓ + 1 ≤ L) {Q : M4} (hQ : Qᴴ = Q) (hc : ∀ x, (par2Enc x)ᴴ * Q * par2Enc x = Q) :
    (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • Q) x) ∈ par2SpanUpTo L tbl G ℓ := by
  set ℓ' : Fin (L + 1) := ⟨ℓ, by omega⟩
  have e : (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • Q) x) =
      fun x => par2Q (par2Blk L tbl G) ℓ' (Complex.I • ((par2Blk L tbl G ℓ)ᴴ * Q * par2Blk L tbl G ℓ)) x := by
    funext x
    rw [par2Q_succ, Matrix.mul_smul, Matrix.smul_mul, hc, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  refine Submodule.span_mono ?_ (par2_herm_mem L tbl htbl G hG ℓ' (conj_herm4 hQ))
  rintro _ ⟨p, rfl⟩
  exact ⟨(ℓ', ⟨0, htbl⟩, p), le_rfl, rfl⟩

theorem par2_word_mem (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (ℓ : ℕ) (hℓ : ℓ + 1 ≤ L) (q : Fin 4 × Fin 4) :
    (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • pw2 q.1 q.2) x) ∈
      par2SpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ)) := by
  have hnew : ∀ k, par2NewFn (par2Blk L tbl G) ℓ k ∈
      par2SpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ)) :=
    fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  have hcomm : ∀ Q : M4, Qᴴ = Q → (∀ x, (par2Enc x)ᴴ * Q * par2Enc x = Q) →
      (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • Q) x) ∈
        par2SpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ)) :=
    fun Q hQ hc => Submodule.mem_sup_left (par2_comm_mem L tbl htbl G hG ℓ hℓ hQ hc)
  have hlow : ∀ a b : Fin 4, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • pw2 a b) x) ∈
        par2SpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ)) :=
    fun a b ha hb => hcomm _ (pw2_herm a b) (fun x => comm_low x a b ha hb)
  have hZZ : (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • pw2 3 3) x) =
      (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • (pw2 2 2 + pw2 3 3)) x) -
        par2NewFn (par2Blk L tbl G) ℓ 8 := by
    funext x
    simp only [par2NewFn, par2New, Pi.sub_apply, smul_add, par2Q_add]
    simp
  have hZY : (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • pw2 3 2) x) =
      (fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • (pw2 3 2 - pw2 2 3)) x) +
        par2NewFn (par2Blk L tbl G) ℓ 9 := by
    funext x
    simp only [par2NewFn, par2New, Pi.add_apply, smul_sub, par2Q_sub]
    simp
  have hYYZZ : (pw2 2 2 + pw2 3 3)ᴴ = pw2 2 2 + pw2 3 3 := by
    rw [Matrix.conjTranspose_add, pw2_herm, pw2_herm]
  have hZYYZ : (pw2 3 2 - pw2 2 3)ᴴ = pw2 3 2 - pw2 2 3 := by
    rw [Matrix.conjTranspose_sub, pw2_herm, pw2_herm]
  obtain ⟨a, b⟩ := q
  fin_cases a <;> fin_cases b
  · exact hlow 0 0 (by decide) (by decide)
  · exact hlow 0 1 (by decide) (by decide)
  · exact hnew 0
  · exact hnew 1
  · exact hlow 1 0 (by decide) (by decide)
  · exact hlow 1 1 (by decide) (by decide)
  · exact hnew 2
  · exact hnew 3
  · exact hnew 4
  · exact hnew 5
  · exact hnew 8
  · exact hnew 9
  · exact hnew 6
  · exact hnew 7
  · exact hZY ▸ Submodule.add_mem _ (hcomm _ hZYYZ comm_ZYYZ) (hnew 9)
  · exact hZZ ▸ Submodule.sub_mem _ (hcomm _ hYYZZ comm_YYZZ) (hnew 8)

theorem par2SpanUpTo_succ_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (ℓ : ℕ) :
    par2SpanUpTo L tbl G (ℓ + 1) ≤
      par2SpanUpTo L tbl G ℓ ⊔ Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ)) := by
  apply Submodule.span_le.2
  rintro f ⟨⟨l, g, p⟩, hl, rfl⟩
  by_cases hlt : (l : ℕ) ≤ ℓ
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨(l, g, p), hlt, rfl⟩)
  have hl' : (l : ℕ) = ℓ + 1 := by simp at hl; omega
  have hℓL : ℓ + 1 ≤ L := by have := l.2; omega
  obtain ⟨D, -, hfun⟩ := par2TangentFn_eq_Q L tbl G hG l g
  set Y := Dᴴ * pauliWord p * D with hYdef
  have hY : Yᴴ = Y := conj_herm4 (pw2_herm _ _)
  have e : parallel2TangentFn L tbl G (l, g, p) = fun x => par2Q (par2Blk L tbl G) (ℓ + 1) (Complex.I • Y) x := by
    funext x
    rw [hfun, hl', hYdef, Matrix.mul_smul, Matrix.smul_mul]
  rw [SetLike.mem_coe, e, herm_decomp4 Y hY, par2Q_sum_fn]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (par2_word_mem L tbl htbl G hG ℓ hℓL q)

theorem par2SpanUpTo_finrank_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    ∀ ℓ, ℓ ≤ L → Module.finrank ℝ (par2SpanUpTo L tbl G ℓ) ≤ 10 * ℓ + 6
  | 0, _ => by
    refine (Submodule.finrank_mono (par2SpanUpTo_zero_le L tbl G hG)).trans ?_
    exact (LinearMap.finrank_range_le _).trans (by rw [par2Const_finrank])
  | ℓ + 1, hℓ => by
    have ih := par2SpanUpTo_finrank_le L tbl htbl G hG ℓ (by omega)
    haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ))) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    refine (Submodule.finrank_mono (par2SpanUpTo_succ_le L tbl htbl G hG ℓ)).trans ?_
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    have h2 := finrank_range_le_card (R := ℝ) (par2NewFn (par2Blk L tbl G) ℓ)
    simp only [Fintype.card_fin] at h2
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (par2NewFn (par2Blk L tbl G) ℓ))) ≤ 10 at h2
    omega

/-- **Proposition 4.4(iii), upper bound.** At most `6 + 10L = 5E + 6` tangent directions, for every choice of gates. -/
theorem parallel2_tangent_rank_le (L tbl : ℕ) (htbl : 1 ≤ tbl) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    parallel2TangentRank L tbl G ≤ 10 * L + 6 := by
  -- PROVIDED SOLUTION
  -- As `serial_tangent_rank_le`, with the encoding S(x) = par2Enc x = e^{−ix}Π₂ + Π₀ + e^{ix}Π₋₂, where
  -- Π₂ = |++⟩⟨++|, Π₋₂ = |−−⟩⟨−−| (|±⟩ = (e₀ ± e₁)/√2) and Π₀ = 1 − Π₂ − Π₋₂ (rank 2), the spectral projections of
  -- X⊗1 + 1⊗X. (1) For the coordinate j in block ℓ, h_j(x) = i·(⟨r, V_ℓ(x)ᴴ Y V_ℓ(x) e₀₀⟩)_{r ≠ 00} with Y Hermitian
  -- (V_ℓ = circuit up to block ℓ; parallel2State = V_L e₀₀, parallel2Unitary = V_L). (2) Block 0 gives constant functions in
  -- ℂ³: dimension ≤ 6. (3) Block ℓ ≥ 1: V_ℓ = B_ℓ S V_{ℓ−1}; with K = B_ℓᴴ Y B_ℓ, Sᴴ K S = Σ_{a,b} e^{i(a−b)x/2} Π_a K Π_b.
  -- The block-diagonal part K₀ = Σ_a Π_a K Π_a commutes with S and its contribution i·π(V_{ℓ−1}ᴴ K₀ V_{ℓ−1}) is a real
  -- combination of block-(ℓ−1) functions (the conjugated Pauli words of the last gate of block ℓ−1 span the traceless
  -- Hermitian matrices; the trace part gives ⟨r, e₀₀⟩ = 0). The off-diagonal remainder depends real-linearly on the
  -- blocks Π_a K Π_b, a ≠ b, of a Hermitian K: real dimension 16 − (1 + 4 + 1) = 10. So dim T_ℓ ≤ dim T_{ℓ−1} + 10.
  refine le_trans ?_ (par2SpanUpTo_finrank_le L tbl htbl G hG L le_rfl)
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨j, Nat.lt_succ_iff.1 j.1.2, rfl⟩

theorem par2Pre_ones (ℓ : ℕ) (x : ℝ) : par2Pre (fun _ => 1) ℓ x = par2Enc (ℓ * x) := by
  induction ℓ with
  | zero => simp [par2Pre, par2Enc_zero]
  | succ ℓ ih =>
    simp only [par2Pre, ih, Matrix.one_mul, par2Enc_add]
    congr 1; push_cast; ring

theorem parallel2TangentFn_ones (L tbl : ℕ) (j : AIdx L tbl) (x : ℝ) :
    parallel2TangentFn L tbl (fun _ => 1) j x = par2Q (fun _ => 1) j.1 (Complex.I • pauliWord j.2.2) x := by
  obtain ⟨l, g, p⟩ := j
  funext r
  rw [parallel2TangentFn_eq]
  have hU : ancillaBlocks L tbl (fun _ => (1 : M4)) = fun _ => 1 := by
    funext ℓ; exact blockProd_ones tbl
  have hP : ancillaBlocks L tbl (perturb (fun _ => (1 : M4)) (l, g) (1 * (Complex.I • pauliWord p))) =
      Function.update (fun _ => 1) l (Complex.I • pauliWord p) := by
    rw [Matrix.one_mul]; exact blocks_perturb_ones L tbl l g _
  obtain ⟨Down, hDS, hDown⟩ := parallel2_update L (fun _ => (1 : M4)) (fun _ => 1) (fun _ => rfl) l
  have e1 : parallel2Unitary L (fun _ => (1 : M4)) x = (Down x * 1) * par2Pre (fun _ => 1) l x := by
    conv_lhs => rw [← Function.update_eq_self l (fun _ => (1 : M4))]
    rw [(hDown _ x).2, Matrix.mul_assoc]
  have e2 : parallel2State L (Function.update (fun _ => 1) l (Complex.I • pauliWord p)) x =
      (Down x * 1) *ᵥ ((Complex.I • pauliWord p) *ᵥ (par2Pre (fun _ => 1) l x *ᵥ ket00)) := by
    rw [(hDown _ x).1, Matrix.mul_one]
  rw [hU, hP, col_eq_mulVec, e1, e2, frame_dot _ _ _ (mul_mem (hDS (fun _ => one_mem _) x) (one_mem _))]
  rfl

/-- Witness function: `i (R_X(θ)ᴴ σ_a R_X(θ))_{r₁0} (R_X(θ)ᴴ σ_b R_X(θ))_{r₂0}`. -/
def par2Wit (θ : ℝ) (a b : Fin 4) (r : Fin 3) : ℂ :=
  Complex.I * ((RXm θ)ᴴ * pauli1 a * RXm θ) (frameIdx r).1 0 * ((RXm θ)ᴴ * pauli1 b * RXm θ) (frameIdx r).2 0

theorem par2Q_ones (ℓ : ℕ) (a b : Fin 4) (x : ℝ) (r : Fin 3) :
    par2Q (fun _ => 1) ℓ (Complex.I • pw2 a b) x r = par2Wit (ℓ * x) a b r := by
  simp only [par2Q, par2Pre_ones, Matrix.mul_smul, Matrix.smul_mul, par2Enc_conj_pw2, par2Wit]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]

/-- Frequency factor of the ten words: `1` for `IY, …, ZX`, `2` for `YY, YZ`. -/
def par2F (t : Fin 10) : ℕ := if (t : ℕ) < 8 then 1 else 2

def par2Gc : Fin 10 → Fin 3 → ℂ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, ![0, 0, -Complex.I / 2], ![1 / 2, -1 / 2, 0]]

def par2Al : Fin 10 → Fin 3 → ℂ :=
  ![![-1, 0, 0], 0, ![0, 0, -1], ![0, Complex.I, 0], ![0, -1, 0], ![0, 0, -1], 0, ![Complex.I, 0, 0],
    ![0, 0, -Complex.I / 2], ![-1 / 2, -1 / 2, 0]]

def par2Be : Fin 10 → Fin 3 → ℂ :=
  ![0, ![-1, 0, 0], ![0, -Complex.I, 0], ![0, 0, -1], 0, ![-Complex.I, 0, 0], ![0, -1, 0], ![0, 0, -1],
    ![1 / 2, 1 / 2, 0], ![0, 0, -Complex.I / 2]]

/-- Column `0` of `R_X(θ)ᴴ σ_k R_X(θ)`. -/
def rxCol (θ : ℝ) : Fin 4 → Fin 2 → ℂ :=
  ![![1, 0], ![0, 1], ![-(Real.sin θ : ℂ), Complex.I * (Real.cos θ : ℂ)],
    ![(Real.cos θ : ℂ), Complex.I * (Real.sin θ : ℂ)]]

theorem rxCol_eq (θ : ℝ) (k : Fin 4) (i : Fin 2) : ((RXm θ)ᴴ * pauli1 k * RXm θ) i 0 = rxCol θ k i := by
  fin_cases k
  · show ((RXm θ)ᴴ * pauli1 0 * RXm θ) i 0 = rxCol θ 0 i
    rw [rx_conj_I]; fin_cases i <;> simp [rxCol, pauli1]
  · show ((RXm θ)ᴴ * pauli1 1 * RXm θ) i 0 = rxCol θ 1 i
    rw [rx_conj_X]; fin_cases i <;> simp [rxCol, pauli1]
  · show ((RXm θ)ᴴ * pauli1 2 * RXm θ) i 0 = rxCol θ 2 i
    rw [rx_conj_Y]
    fin_cases i <;> simp [rxCol, pauli1]
    ring
  · show ((RXm θ)ᴴ * pauli1 3 * RXm θ) i 0 = rxCol θ 3 i
    rw [rx_conj_Z]
    fin_cases i <;> simp [rxCol, pauli1]
    ring

theorem par2Wit_new (t : Fin 10) (θ : ℝ) (r : Fin 3) :
    par2Wit θ (par2New t).1 (par2New t).2 r = par2Gc t r + par2Al t r * (Real.cos (par2F t * θ) : ℂ) +
      par2Be t r * (Real.sin (par2F t * θ) : ℂ) := by
  have h1 := Real.cos_sq_add_sin_sq θ
  have hc2 := Real.cos_two_mul θ
  have hs2 := Real.sin_two_mul θ
  rw [par2Wit, rxCol_eq, rxCol_eq]
  fin_cases t <;> fin_cases r <;>
    simp [par2New, rxCol, frameIdx, par2Gc, par2Al, par2Be, par2F, Complex.ext_iff, hc2, hs2, sq,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [h1]


/-- Pauli words used in block `0`: `XI, IX, YI, IY, XY, YY`. -/
def par2W0 : Fin 6 → Fin 4 × Fin 4 := ![(1, 0), (0, 1), (2, 0), (0, 2), (1, 2), (2, 2)]

/-- Values of the block-`0` witness functions. -/
def par2Gam : Fin 6 → Fin 3 → ℂ :=
  ![![0, Complex.I, 0], ![Complex.I, 0, 0], ![0, -1, 0], ![-1, 0, 0], ![0, 0, -1], ![0, 0, -Complex.I]]

theorem par2W0_val (t : Fin 6) (r : Fin 3) :
    (Complex.I • pw2 (par2W0 t).1 (par2W0 t).2) (frameIdx r) (0, 0) = par2Gam t r := by
  fin_cases t <;> fin_cases r <;>
    simp [pw2, Matrix.kronecker, Matrix.kroneckerMap_apply, pauli1, frameIdx, par2W0, par2Gam]

def par2NewW (t : Fin 10) : PWord := ⟨par2New t, by fin_cases t <;> decide⟩

def par2W0W (t : Fin 6) : PWord := ⟨par2W0 t, by fin_cases t <;> decide⟩

/-- The `10L + 6` coordinates used for the lower bound (first gate of each block). -/
def par2WitIdx (L tbl : ℕ) (htbl : 1 ≤ tbl) : Fin 6 ⊕ (Fin L × Fin 10) → AIdx L tbl
  | Sum.inl t => (0, ⟨0, htbl⟩, par2W0W t)
  | Sum.inr (m, t) => (m.succ, ⟨0, htbl⟩, par2NewW t)

theorem par2_wit_inl (L tbl : ℕ) (htbl : 1 ≤ tbl) (t : Fin 6) (x : ℝ) (r : Fin 3) :
    parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl (Sum.inl t)) x r = par2Gam t r := by
  rw [parallel2TangentFn_ones]
  show par2Q (fun _ => 1) ((0 : Fin (L + 1)) : ℕ) (Complex.I • pw2 (par2W0 t).1 (par2W0 t).2) x r = _
  rw [Fin.val_zero, par2Q_zero]
  exact par2W0_val t r

theorem par2F_bound {L : ℕ} (t : Fin 10) (m : Fin L) : 1 ≤ par2F t * (m + 1) ∧ par2F t * (m + 1) ≤ 2 * L := by
  have h : par2F t = 1 ∨ par2F t = 2 := by unfold par2F; split_ifs <;> simp
  have := m.2
  rcases h with h | h <;> rw [h] <;> omega

theorem par2_wit_inr (L tbl : ℕ) (htbl : 1 ≤ tbl) (m : Fin L) (t : Fin 10) (x : ℝ) (r : Fin 3) :
    parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl (Sum.inr (m, t))) x r =
      par2Gc t r + par2Al t r * (Real.cos (((par2F t * (m + 1) : ℕ) : ℝ) * x) : ℂ) +
        par2Be t r * (Real.sin (((par2F t * (m + 1) : ℕ) : ℝ) * x) : ℂ) := by
  rw [parallel2TangentFn_ones]
  show par2Q (fun _ => 1) ((m.succ : Fin (L + 1)) : ℕ) (Complex.I • pw2 (par2New t).1 (par2New t).2) x r = _
  rw [par2Q_ones, par2Wit_new, Fin.val_succ]
  rw [show (par2F t : ℝ) * ((((m : ℕ) + 1 : ℕ) : ℝ) * x) = ((par2F t * ((m : ℕ) + 1) : ℕ) : ℝ) * x by
    push_cast; ring]

/-- Design-matrix coefficients of the samples of the witness functions. -/
def par2Coef (L : ℕ) : Fin 6 ⊕ (Fin L × Fin 10) → Fin 3 → Bool → Fin (2 * (2 * L) + 1) → ℝ
  | Sum.inl t, r, b => Pi.single ⟨0, by omega⟩ (reimB b (par2Gam t r))
  | Sum.inr (m, t), r, b => Pi.single ⟨0, by omega⟩ (reimB b (par2Gc t r)) +
      Pi.single ⟨2 * (par2F t * (m + 1)) - 1, by have := par2F_bound t m; omega⟩ (reimB b (par2Al t r) / 2) +
      Pi.single ⟨2 * (par2F t * (m + 1)), by have := par2F_bound t m; omega⟩ (-reimB b (par2Be t r) / 2)

theorem mulVec_three_single {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (i j l : Fin m) (a c d : ℝ) (k : Fin m) :
    (M *ᵥ (Pi.single i a + Pi.single j c + Pi.single l d)) k = M k i * a + M k j * c + M k l * d := by
  simp [Matrix.mulVec, dotProduct_add, dotProduct_single]

theorem par2Sample_eq (L tbl : ℕ) (htbl : 1 ≤ tbl) (p : Fin 6 ⊕ (Fin L × Fin 10)) (r : Fin 3) (b : Bool)
    (s : Fin (2 * (2 * L) + 1)) :
    ancSampler (2 * L) (parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl p)) (r, b, s) =
      (designMatrix (2 * L) (eqGrid (2 * L) 0) *ᵥ par2Coef L p r b) s := by
  rcases p with t | ⟨m, t⟩
  · have hf : ∀ x, parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl (Sum.inl t)) x r = _ :=
      fun x => par2_wit_inl L tbl htbl t x r
    simp only [ancSampler, LinearMap.coe_mk, AddHom.coe_mk, hf, par2Coef]
    simp [Matrix.mulVec, dotProduct_single, designMatrix]
  · have hf : ∀ x, parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl (Sum.inr (m, t))) x r = _ :=
      fun x => par2_wit_inr L tbl htbl m t x r
    simp only [ancSampler, LinearMap.coe_mk, AddHom.coe_mk, hf, par2Coef]
    rw [mulVec_three_single]
    have hb := par2F_bound t m
    have h1 : (2 * (par2F t * ((m : ℕ) + 1)) - 1 + 1) / 2 = (par2F t * ((m : ℕ) + 1)) := by omega
    have h2 : (2 * (par2F t * ((m : ℕ) + 1)) - 1) % 2 = 1 := by omega
    have h3 : 2 * (par2F t * ((m : ℕ) + 1)) - 1 ≠ 0 := by omega
    have h4 : 2 * (par2F t * ((m : ℕ) + 1)) / 2 = (par2F t * ((m : ℕ) + 1)) := by omega
    have h5 : 2 * (par2F t * ((m : ℕ) + 1)) ≠ 0 := by omega
    have h6 : ¬ (2 * (par2F t * ((m : ℕ) + 1))) % 2 = 1 := by omega
    simp only [designMatrix, h1, h2, h3, h4, h5, h6, if_false, if_true, reimB_add, reimB_ofReal_mul]
    ring


theorem par2Coef_inl_ne (L : ℕ) (t : Fin 6) (r : Fin 3) (b : Bool) (s : Fin (2 * (2 * L) + 1))
    (hs : (s : ℕ) ≠ 0) : par2Coef L (Sum.inl t) r b s = 0 := by
  simp only [par2Coef, Pi.single_apply]
  rw [if_neg (fun h => hs (by rw [h]))]

theorem par2Coef_inl_zero (L : ℕ) (t : Fin 6) (r : Fin 3) (b : Bool) :
    par2Coef L (Sum.inl t) r b ⟨0, by omega⟩ = reimB b (par2Gam t r) := by
  simp [par2Coef]

theorem par2Coef_inr_odd (L : ℕ) (m : Fin L) (t : Fin 10) (r : Fin 3) (b : Bool) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ 2 * L) :
    par2Coef L (Sum.inr (m, t)) r b ⟨2 * k - 1, by omega⟩ =
      if par2F t * ((m : ℕ) + 1) = k then reimB b (par2Al t r) / 2 else 0 := by
  have hb := par2F_bound t m
  simp only [par2Coef, Pi.add_apply, Pi.single_apply, Fin.mk.injEq]
  by_cases h : par2F t * ((m : ℕ) + 1) = k
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h]; ring

theorem par2Coef_inr_even (L : ℕ) (m : Fin L) (t : Fin 10) (r : Fin 3) (b : Bool) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ 2 * L) :
    par2Coef L (Sum.inr (m, t)) r b ⟨2 * k, by omega⟩ =
      if par2F t * ((m : ℕ) + 1) = k then -reimB b (par2Be t r) / 2 else 0 := by
  have hb := par2F_bound t m
  simp only [par2Coef, Pi.add_apply, Pi.single_apply, Fin.mk.injEq]
  by_cases h : par2F t * ((m : ℕ) + 1) = k
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h]; ring

/-- Finite fact (F1–F3): the frequency-`±k` coefficient vectors of the ten words are ℝ-linearly independent. -/
theorem par2_F3 (a : Fin 10 → ℝ) (hα : ∀ r b, ∑ t, a t * (reimB b (par2Al t r) / 2) = 0)
    (hβ : ∀ r b, ∑ t, a t * (-reimB b (par2Be t r) / 2) = 0) : ∀ t, a t = 0 := by
  have e1 := hα 0 true
  have e2 := hα 0 false
  have e3 := hα 1 true
  have e4 := hα 1 false
  have e5 := hα 2 true
  have e6 := hα 2 false
  have f1 := hβ 0 true
  have f2 := hβ 0 false
  have f3 := hβ 1 true
  have f4 := hβ 1 false
  have f5 := hβ 2 true
  have f6 := hβ 2 false
  simp [Fin.sum_univ_succ, par2Al, par2Be, reimB] at e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6
  intro t
  fin_cases t <;> simp <;> linarith

/-- Finite fact (F4): the six block-`0` constants are ℝ-linearly independent. -/
theorem par2_F4 (a : Fin 6 → ℝ) (h : ∀ r b, ∑ t, a t * reimB b (par2Gam t r) = 0) : ∀ t, a t = 0 := by
  have e1 := h 0 true
  have e2 := h 0 false
  have e3 := h 1 true
  have e4 := h 1 false
  have e5 := h 2 true
  have e6 := h 2 false
  simp [Fin.sum_univ_succ, par2Gam, reimB] at e1 e2 e3 e4 e5 e6
  intro t
  fin_cases t <;> simp <;> linarith

theorem par2_witness_linInd (L tbl : ℕ) (htbl : 1 ≤ tbl) :
    LinearIndependent ℝ (fun p => ancSampler (2 * L)
      (parallel2TangentFn L tbl (fun _ => 1) (par2WitIdx L tbl htbl p))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcomp : ∀ r b, ∑ p, g p • par2Coef L p r b = 0 := by
    intro r b
    apply Matrix.eq_zero_of_mulVec_eq_zero (design_det_ne_zero (2 * L) 0)
    funext k
    have := congrFun hg (r, b, k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, par2Sample_eq] at this
    have e : designMatrix (2 * L) (eqGrid (2 * L) 0) *ᵥ ∑ p, g p • par2Coef L p r b =
        ∑ p, g p • (designMatrix (2 * L) (eqGrid (2 * L) 0) *ᵥ par2Coef L p r b) := by
      simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [e]
    simpa [Finset.sum_apply] using this
  have hs : ∀ r b (s : Fin (2 * (2 * L) + 1)), ∑ p, g p * par2Coef L p r b s = 0 := by
    intro r b s
    have := congrFun (hcomp r b) s
    simpa [Finset.sum_apply] using this
  have hinr : ∀ m0 t0, g (Sum.inr (m0, t0)) = 0 := by
    intro m0 t0
    have hb := par2F_bound t0 m0
    set k := par2F t0 * ((m0 : ℕ) + 1) with hk
    set a : Fin 10 → ℝ := fun t => ∑ m : Fin L,
      if par2F t * ((m : ℕ) + 1) = k then g (Sum.inr (m, t)) else 0 with ha
    have hα : ∀ r b, ∑ t, a t * (reimB b (par2Al t r) / 2) = 0 := by
      intro r b
      have := hs r b ⟨2 * k - 1, by omega⟩
      have h1 : ∀ t, par2Coef L (Sum.inl t) r b ⟨2 * k - 1, by omega⟩ = 0 :=
        fun t => par2Coef_inl_ne L t r b _ (by simp only; omega)
      have h2 : ∀ m t, par2Coef L (Sum.inr (m, t)) r b ⟨2 * k - 1, by omega⟩ =
          if par2F t * ((m : ℕ) + 1) = k then reimB b (par2Al t r) / 2 else 0 :=
        fun m t => par2Coef_inr_odd L m t r b k hb.1 hb.2
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at this
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add] at this
      rw [Finset.sum_comm] at this
      rw [← this]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    have hβ : ∀ r b, ∑ t, a t * (-reimB b (par2Be t r) / 2) = 0 := by
      intro r b
      have := hs r b ⟨2 * k, by omega⟩
      have h1 : ∀ t, par2Coef L (Sum.inl t) r b ⟨2 * k, by omega⟩ = 0 :=
        fun t => par2Coef_inl_ne L t r b _ (by simp only; omega)
      have h2 : ∀ m t, par2Coef L (Sum.inr (m, t)) r b ⟨2 * k, by omega⟩ =
          if par2F t * ((m : ℕ) + 1) = k then -reimB b (par2Be t r) / 2 else 0 :=
        fun m t => par2Coef_inr_even L m t r b k hb.1 hb.2
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at this
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add] at this
      rw [Finset.sum_comm] at this
      rw [← this]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    have h0 := par2_F3 a hα hβ t0
    have hat : a t0 = g (Sum.inr (m0, t0)) := by
      simp only [ha]
      rw [Finset.sum_eq_single m0]
      · rw [if_pos rfl]
      · intro m _ hm
        rw [if_neg]
        intro h
        apply hm
        have hF : 0 < par2F t0 := by have := hb.1; unfold par2F at this ⊢; split_ifs <;> omega
        exact Fin.ext (by have := Nat.eq_of_mul_eq_mul_left hF h; omega)
      · simp
    rw [← hat, h0]
  have hinl : ∀ t0, g (Sum.inl t0) = 0 := by
    refine par2_F4 _ fun r b => ?_
    have := hs r b ⟨0, by omega⟩
    rw [Fintype.sum_sum_type] at this
    simp only [hinr, zero_mul, Finset.sum_const_zero, add_zero, par2Coef_inl_zero] at this
    exact this
  rintro (t | ⟨m, t⟩)
  · exact hinl t
  · exact hinr m t


theorem IsCPoly.parallel2Unitary {ι n : Type*} (x : ℝ) (L : ℕ) :
    ∀ (V : (ι → Matrix n n ℂ) → Fin (L + 1) → M4),
    (∀ ℓ a b, IsCPoly (fun G => V G ℓ a b)) →
      ∀ a b, IsCPoly (fun G => _root_.parallel2Unitary L (V G) x a b) := by
  induction L with
  | zero => intro V h a b; exact h 0 a b
  | succ L ih =>
    intro V h a b
    have h1 := ih (fun G ℓ => V G (Fin.castSucc ℓ)) (fun ℓ => h _)
    have h2 := IsCPoly.matMul (M := fun _ => par2Enc x) (fun a b => IsCPoly.const _) h1
    exact IsCPoly.matMul (M := fun G => V G (Fin.last (L + 1))) (h _) h2 a b

theorem IsCPoly.parallel2State {ι n : Type*} (x : ℝ) (L : ℕ) :
    ∀ (V : (ι → Matrix n n ℂ) → Fin (L + 1) → M4),
    (∀ ℓ a b, IsCPoly (fun G => V G ℓ a b)) → ∀ i, IsCPoly (fun G => _root_.parallel2State L (V G) x i) := by
  induction L with
  | zero =>
    intro V h i
    exact IsCPoly.mulVec (M := fun G => V G 0) (v := fun _ => ket00) (h 0) (fun b => IsCPoly.const _) i
  | succ L ih =>
    intro V h i
    have h1 := ih (fun G ℓ => V G (Fin.castSucc ℓ)) (fun ℓ => h _)
    have h2 := IsCPoly.mulVec (M := fun _ => par2Enc x) (fun a b => IsCPoly.const _) h1
    exact IsCPoly.mulVec (M := fun G => V G (Fin.last (L + 1))) (h _) h2 i

theorem parallel2TangentFn_isCPoly (L tbl : ℕ) (j : AIdx L tbl) (x : ℝ) (r : Fin 3) :
    IsCPoly (fun G : Gates L tbl (Fin 2 × Fin 2) => parallel2TangentFn L tbl G j x r) := by
  have hblk : ∀ (F : Gates L tbl (Fin 2 × Fin 2) → Gates L tbl (Fin 2 × Fin 2)),
      (∀ i a b, IsCPoly (fun G => F G i a b)) → ∀ ℓ a b,
      IsCPoly (fun G => ancillaBlocks L tbl (F G) ℓ a b) := by
    intro F hF ℓ a b
    exact IsCPoly.blockProd tbl (fun G g => F G (ℓ, g)) (fun g => hF _) a b
  have hU := IsCPoly.parallel2Unitary x L _ (hblk id (fun i a b => IsCPoly.entry i a b))
  have hv := IsCPoly.parallel2State x L _
    (hblk _ (IsCPoly.perturb_mul (j.1, j.2.1) (Complex.I • pauliWord j.2.2)))
  refine (IsCPoly.sum Finset.univ fun a _ => (hU a (frameIdx r)).conj.mul (hv a)).congr fun G => ?_
  rw [parallel2TangentFn_eq]
  simp [dotProduct]

/-- **Proposition 4.4(iii), equality almost everywhere.** -/
theorem parallel2_tangent_rank_generic (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      parallel2TangentRank L tbl (fun i => Matrix.of (G i)) ≠ 10 * L + 6} = 0 := by
  -- PROVIDED SOLUTION
  -- By `parallel2_tangent_rank_le` the set is {rank < 10L + 6}; apply `tangent_rank_generic_of_witness` (as for
  -- `ancilla_tangent_rank_generic`) with the witness "all gates = 1" and the following 10L + 6 coordinates
  -- (Pauli words written qubit 0 first, pauli1: 0 = I, 1 = X, 2 = Y, 3 = Z; gate 0 of each block):
  --   block 0:      XI, IX, YI, IY, XY, YY
  --   block ℓ ≥ 1:  IY, IZ, XY, XZ, YI, YX, ZI, ZX  (group A)  and  YY, YZ  (group B)
  -- At identity gates V_ℓ(x) = S(x)^ℓ = S(ℓx) (RXm x)^ℓ = RXm (ℓx)), so the block-ℓ function of a word P is g_P(ℓx) with
  -- g_P(θ) = i·(⟨r, S(θ)ᴴ P S(θ) e₀₀⟩)_{r ≠ 00}, independent of ℓ. Explicitly (conjugation by RXm rotates Y, Z and fixes
  -- I, X on each qubit): group-A words have Fourier coefficients only at θ-frequencies ±1, group-B words at ±2 and 0,
  -- block-0 words are constants. Finite facts to check on the explicit g_P (each an equality of small complex vectors):
  --   (F1) the coefficient vectors at frequencies (+1, −1) ∈ ℂ³ × ℂ³ of the 8 group-A words are ℝ-linearly independent;
  --   (F2) the coefficient vectors at (+2, −2) of YY, YZ are ℝ-linearly independent;
  --   (F3) the ℝ-span of (F1)'s vectors and that of (F2)'s vectors (both in ℂ³ × ℂ³) meet only in 0 (joint rank 10);
  --   (F4) the 6 constants i(⟨r, P e₀₀⟩)_{r ≠ 00} of the block-0 words are ℝ-linearly independent.
  -- Independence: take a vanishing real combination Σ a_{ℓ,P} g_P(ℓx) and read off the Fourier coefficient at the frequency
  -- pair ±k (k ≥ 1): it is (group-A part of block k, if k ≤ L) + (group-B part of block k/2, if k even). By (F3) both parts
  -- vanish, so by (F1), (F2) every a_{ℓ,P} with ℓ ≥ 1 is 0; then (F4) kills block 0. For the linear map `E` use the real
  -- and imaginary parts of the samples on 4L + 1 equispaced points (the functions have degree ≤ 2L), as in the ancilla case.
  refine MeasureTheory.measure_mono_null ?_ (tangent_rank_generic_of_witness (parallel2TangentFn L tbl)
    (ancSampler (2 * L)) (par2WitIdx L tbl htbl) (fun a q => ?_) (fun _ => 1) (fun _ => one_mem _)
    (par2_witness_linInd L tbl htbl) μ hμ)
  · rintro G ⟨hSU, hne⟩
    refine ⟨hSU, ?_⟩
    have := parallel2_tangent_rank_le L tbl htbl _ hSU
    unfold parallel2TangentRank at this hne
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  · obtain ⟨r, b, k⟩ := q
    cases b
    · exact (parallel2TangentFn_isCPoly L tbl (par2WitIdx L tbl htbl a) (eqGrid (2 * L) 0 k) r).2.congr
        fun G => by simp [ancSampler, reimB]
    · exact (parallel2TangentFn_isCPoly L tbl (par2WitIdx L tbl htbl a) (eqGrid (2 * L) 0 k) r).1.congr
        fun G => by simp [ancSampler, reimB]

end

end


/-! # Section 23: Remark 4.3 (norm, adapted basis, change of basis) and Corollary 4.5(i), (ii) -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 23. Envelope norm, rotation about the readout axis, no spare tangent direction -/

/-! ### Remark 4.3: norm of the envelopes, adapted basis, change of frame -/

open scoped InnerProductSpace in
/-- **Remark 4.3, norm.** If `M` is self-adjoint with `M² = 1`, the envelopes `μ_r = ⟨b r, M ψ⟩`, `r ≥ 1`, of the unit
    state `ψ = b 0` satisfy `Σ_r |μ_r|² = 1 − f²` with `f = ⟨ψ, Mψ⟩`, in every dimension. -/
theorem multi_qubit_envelope_normSq {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℂ (EuclideanSpace ℂ (Fin (d + 1))))
    (M : EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1))) (hM : M.IsSymmetric)
    (hM2 : ∀ v, M (M v) = v) :
    (∑ r : Fin d, Complex.normSq ⟪b r.succ, M (b 0)⟫_ℂ) = 1 - ((⟪b 0, M (b 0)⟫_ℂ).re) ^ 2 := by
  -- PROVIDED SOLUTION
  -- Parseval in the orthonormal basis b: Σ_{r : Fin (d+1)} ‖⟪b r, M (b 0)⟫‖² = ‖M (b 0)‖²
  -- (`OrthonormalBasis.sum_sq_norm_inner_right`, or `b.sum_inner_mul_inner (M (b 0)) (M (b 0))` as in
  -- `multi_qubit_envelopes`). ‖M (b 0)‖² = re ⟪M (b 0), M (b 0)⟫ = re ⟪b 0, M (M (b 0))⟫ (hM) = re ⟪b 0, b 0⟫ (hM2) = 1.
  -- Split off r = 0 with `Fin.sum_univ_succ`. ⟪b 0, M (b 0)⟫ is real (`hreal` in the proof of `multi_qubit_envelopes`),
  -- so its normSq is re². `Complex.normSq_eq_norm_sq` converts between normSq and ‖·‖².
  have hpars := b.sum_sq_norm_inner_right (M (b 0))
  have hn : ‖M (b 0)‖ ^ 2 = 1 := by
    have h1 : ⟪M (b 0), M (b 0)⟫_ℂ = ⟪b 0, M (M (b 0))⟫_ℂ := hM _ _
    rw [hM2] at h1
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (M (b 0)), h1, ← norm_sq_eq_re_inner (𝕜 := ℂ), b.orthonormal.1 0]
    norm_num
  have hreal : (⟪b 0, M (b 0)⟫_ℂ).im = 0 := by
    have h := hM (b 0) (b 0)
    rw [← inner_conj_symm] at h
    exact Complex.conj_eq_iff_im.mp h
  rw [hn, Fin.sum_univ_succ] at hpars
  simp only [← Complex.normSq_eq_norm_sq] at hpars
  rw [Complex.normSq_apply, hreal] at hpars
  linarith

open scoped InnerProductSpace in
/-- **Remark 4.3, `μ_r = ⟨e_r, (M − f) ψ⟩`.** -/
theorem multi_qubit_envelope_shift {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℂ (EuclideanSpace ℂ (Fin (d + 1))))
    (M : EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1))) (r : Fin d) :
    ⟪b r.succ, M (b 0)⟫_ℂ = ⟪b r.succ, M (b 0) - (((⟪b 0, M (b 0)⟫_ℂ).re : ℝ) : ℂ) • b 0⟫_ℂ := by
  -- PROVIDED SOLUTION
  -- `inner_sub_right`, `inner_smul_right`, and ⟪b r.succ, b 0⟫ = 0 by orthonormality (`b.orthonormal`, r.succ ≠ 0).
  rw [inner_sub_right, inner_smul_right, b.orthonormal.inner_eq_zero (Fin.succ_ne_zero r), mul_zero,
    sub_zero]

open scoped InnerProductSpace in
/-- **Remark 4.3, adapted basis.** If `(M − f) ψ` is a multiple of `b 1`, every envelope `μ_r` with `r ≥ 2` vanishes:
    the number of non-zero envelopes depends on the basis. -/
theorem multi_qubit_adapted_basis {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 2)) ℂ (EuclideanSpace ℂ (Fin (d + 2))))
    (M : EuclideanSpace ℂ (Fin (d + 2)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 2))) (c : ℂ)
    (hb : M (b 0) - (((⟪b 0, M (b 0)⟫_ℂ).re : ℝ) : ℂ) • b 0 = c • b 1)
    (r : Fin (d + 2)) (hr : 2 ≤ (r : ℕ)) : ⟪b r, M (b 0)⟫_ℂ = 0 := by
  -- PROVIDED SOLUTION
  -- From hb: M (b 0) = f • b 0 + c • b 1 (`sub_eq_iff_eq_add`). Then ⟪b r, M (b 0)⟫ = f ⟪b r, b 0⟫ + c ⟪b r, b 1⟫ = 0,
  -- since r ≠ 0 and r ≠ 1 (from hr, compare `Fin.val`) and b is orthonormal (`inner_add_right`, `inner_smul_right`).
  rw [sub_eq_iff_eq_add] at hb
  have h0 : r ≠ 0 := fun h => by subst h; simp at hr
  have h1 : r ≠ 1 := fun h => by subst h; simp at hr
  rw [hb, inner_add_right, inner_smul_right, inner_smul_right, b.orthonormal.inner_eq_zero h0,
    b.orthonormal.inner_eq_zero h1]
  simp

open scoped InnerProductSpace in
/-- **Remark 4.3, change of frame.** Two orthonormal bases with the same first vector `ψ`: the coordinates of any
    vector in the second frame of `ψ^⊥` are those in the first, multiplied by one unitary matrix that does not depend
    on the vector. -/
theorem multi_qubit_frame_change {d : ℕ}
    (b b' : OrthonormalBasis (Fin (d + 1)) ℂ (EuclideanSpace ℂ (Fin (d + 1)))) (h0 : b' 0 = b 0)
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    (fun r : Fin d => ⟪b' r.succ, v⟫_ℂ) =
        (Matrix.of (fun r s : Fin d => ⟪b' r.succ, b s.succ⟫_ℂ) : Matrix (Fin d) (Fin d) ℂ) *ᵥ
          (fun s : Fin d => ⟪b s.succ, v⟫_ℂ) ∧
      (Matrix.of (fun r s : Fin d => ⟪b' r.succ, b s.succ⟫_ℂ) : Matrix (Fin d) (Fin d) ℂ) ∈
        Matrix.unitaryGroup (Fin d) ℂ := by
  -- PROVIDED SOLUTION
  -- First part: `b.sum_inner_mul_inner (b' r.succ) v : Σ_{i : Fin (d+1)} ⟪b' r.succ, b i⟫ * ⟪b i, v⟫ = ⟪b' r.succ, v⟫`;
  -- split off i = 0 with `Fin.sum_univ_succ`; ⟪b' r.succ, b 0⟫ = ⟪b' r.succ, b' 0⟫ = 0 (h0, orthonormality of b').
  -- What remains is the definition of `Matrix.mulVec` (`Matrix.mulVec`, `dotProduct`, `Matrix.of_apply`).
  -- Second part: `Matrix.mem_unitaryGroup_iff` (W * star W = 1). Entry (r, r'):
  -- Σ_s ⟪b' r.succ, b s.succ⟫ * conj ⟪b' r'.succ, b s.succ⟫ = Σ_s ⟪b' r.succ, b s.succ⟫ * ⟪b s.succ, b' r'.succ⟫
  -- (`inner_conj_symm`); add the vanishing term s = 0 and use `b.sum_inner_mul_inner (b' r.succ) (b' r'.succ)`
  -- to get ⟪b' r.succ, b' r'.succ⟫ = if r = r' then 1 else 0 (`orthonormal_iff_ite`, `Fin.succ_inj`).
  have hz : ∀ r : Fin d, ⟪b' r.succ, b 0⟫_ℂ = 0 := fun r => by
    rw [← h0]; exact b'.orthonormal.inner_eq_zero (Fin.succ_ne_zero r)
  have hexp : ∀ r : Fin d, ∀ w,
      ⟪b' r.succ, w⟫_ℂ = ∑ s : Fin d, ⟪b' r.succ, b s.succ⟫_ℂ * ⟪b s.succ, w⟫_ℂ := by
    intro r w
    rw [← b.sum_inner_mul_inner (b' r.succ) w, Fin.sum_univ_succ, hz, zero_mul, zero_add]
  refine ⟨?_, ?_⟩
  · funext r
    rw [hexp r v]
    simp [Matrix.mulVec, dotProduct]
  · rw [Matrix.mem_unitaryGroup_iff]
    ext r r'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, RCLike.star_def, inner_conj_symm,
      Matrix.one_apply]
    rw [← hexp r (b' r'.succ), orthonormal_iff_ite.mp b'.orthonormal]
    simp [Fin.succ_inj]

/-- **Remark 4.3, invariance.** Multiplying all tangent-coefficient functions by one unitary matrix `V x` (a change of
    orthonormal frame of `ψ(x)^⊥`, `multi_qubit_frame_change`) does not change the real dimension of their span. -/
theorem tangent_span_frame_invariant {J : Type*} {n : ℕ} (h : J → ℝ → Fin n → ℂ)
    (V : ℝ → Matrix (Fin n) (Fin n) ℂ) (hV : ∀ x, V x ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : J => fun x : ℝ => V x *ᵥ h j x))) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range h)) := by
  -- PROVIDED SOLUTION
  -- Let Φ : (ℝ → Fin n → ℂ) ≃ₗ[ℝ] (ℝ → Fin n → ℂ), Φ g x = V x *ᵥ g x, with inverse g ↦ (x ↦ star (V x) *ᵥ g x)
  -- (use `Matrix.mem_unitaryGroup_iff`, `Matrix.mem_unitaryGroup_iff'`, `Matrix.mulVec_mulVec`, `Matrix.one_mulVec`).
  -- The family on the left is Φ ∘ h, so its span is `Submodule.map Φ (span (range h))` (`Submodule.map_span`,
  -- `Set.range_comp`), and `LinearEquiv.finrank_map_eq` finishes.
  let Φ : (ℝ → Fin n → ℂ) ≃ₗ[ℝ] (ℝ → Fin n → ℂ) :=
    { toFun := fun g x => V x *ᵥ g x
      invFun := fun g x => star (V x) *ᵥ g x
      map_add' := fun f g => by funext x; simp [Matrix.mulVec_add]
      map_smul' := fun c g => by
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [← Matrix.mulVec_smul]
      left_inv := fun g => by
        funext x
        simp only [Matrix.mulVec_mulVec, (Matrix.mem_unitaryGroup_iff').mp (hV x), Matrix.one_mulVec]
      right_inv := fun g => by
        funext x
        simp only [Matrix.mulVec_mulVec, (Matrix.mem_unitaryGroup_iff).mp (hV x), Matrix.one_mulVec] }
  have : Submodule.span ℝ (Set.range (fun j : J => fun x : ℝ => V x *ᵥ h j x)) =
      Submodule.map (Φ : (ℝ → Fin n → ℂ) →ₗ[ℝ] (ℝ → Fin n → ℂ)) (Submodule.span ℝ (Set.range h)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [this, LinearEquiv.finrank_map_eq]

/-! ### Remark 4.3(ii) for one qubit and Corollary 4.5(i): envelope norm, rotation about the readout axis -/

/-- Algebraic core of Remark 4.3(ii) for one qubit: for a unit `ψ ∈ ℂ²`, `|⟨Tψ, Zψ⟩|² = 1 − ⟨ψ, Zψ⟩²`. -/
theorem envelope_normSq (ψ : Fin 2 → ℂ) (hψ : ip ψ ψ = 1) :
    Complex.normSq (ip (T ψ) (Zm *ᵥ ψ)) = 1 - ((ip ψ (Zm *ᵥ ψ)).re) ^ 2 := by
  -- PROVIDED SOLUTION
  -- Write a = ψ 0, b = ψ 1. hψ says |a|² + |b|² = 1 (real parts: a.re² + a.im² + b.re² + b.im² = 1).
  -- Zm *ᵥ ψ = (a, −b); T ψ = (−conj b, conj a); ip (T ψ) (Zm *ᵥ ψ) = conj(−conj b)·a + conj(conj a)·(−b) = −2ab.
  -- So normSq = 4 |a|² |b|². (ip ψ (Zm *ᵥ ψ)).re = |a|² − |b|² (`ip_Zm_re`). Then
  -- 1 − (|a|² − |b|²)² = (|a|² + |b|²)² − (|a|² − |b|²)² = 4 |a|² |b|². Finish with
  -- `simp [ip, T, Zm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_apply, Complex.ext_iff] at *`, `nlinarith`.
  simp [ip, T, Zm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_apply, Complex.ext_iff] at *
  nlinarith [hψ]

/-- **Remark 4.3(ii) for one qubit.** `|μ(x)|² = 1 − f(x)²` for the serial circuit. -/
theorem gate_envelope_normSq (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (x : ℝ) :
    Complex.normSq (gateMu L tbl G x) = 1 - (gateModel L tbl G x) ^ 2 := by
  -- PROVIDED SOLUTION
  -- `unfold gateMu gateModel` and apply `envelope_normSq` to `gateState L tbl G x`, which is a unit vector by
  -- `gateState_normalised L tbl G (fun i => (hG i).1) x`.
  unfold gateMu gateModel
  exact envelope_normSq _ (gateState_normalised L tbl G (fun i => (hG i).1) x)

/-- The curve `s ↦ e^{isZ} V = (cos s · 1 + i sin s · Z) V` through a gate `V`: rotation about the readout axis. -/
def readoutCurve (V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.cos s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * (Real.sin s : ℂ)) • Zm) * V

/-- The last gate (block `L`, last gate of the block) is the leftmost factor of the circuit: replacing it by `A * V`
    multiplies the state by `A`. -/
theorem gateState_last_mul (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    gateState L (t + 1) (perturb G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t))) x =
      A *ᵥ gateState L (t + 1) G x := by
  -- PROVIDED SOLUTION
  -- `unfold gateState perturb`. `blockProd (t+1) g = g (Fin.last t) * blockProd t (fun i => g (Fin.castSucc i))`, and
  -- `serialState` applies block `Fin.last L` last: for L = 0 the state is `V 0 *ᵥ ![1, 0]` (and `Fin.last 0 = 0`), for
  -- L + 1 it is `V (Fin.last (L+1)) *ᵥ (RXm x *ᵥ serialState L (fun i => V (Fin.castSucc i)) x)`. So `cases L`.
  -- With `Function.update_self` the updated block is `(A * G i₀) * blockProd t _ = A * (G i₀ * blockProd t _)`
  -- (`Matrix.mul_assoc`), and every other gate is unchanged: `Function.update_of_ne`, because
  -- `(ℓ, Fin.castSucc g) ≠ (ℓ, Fin.last t)` (`Fin.castSucc_lt_last`, `ne_of_lt`) and
  -- `(Fin.castSucc ℓ, g) ≠ (Fin.last _, _)`. Finish with `Matrix.mulVec_mulVec`.
  have hblk : (fun ℓ => blockProd (t + 1) (fun g =>
      perturb G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t)) (ℓ, g))) =
      Function.update (fun ℓ => blockProd (t + 1) (fun g => G (ℓ, g))) (Fin.last L)
        (A * blockProd (t + 1) (fun g => G (Fin.last L, g))) := by
    funext ℓ
    by_cases hℓ : ℓ = Fin.last L
    · subst hℓ
      rw [Function.update_self]
      have e : (fun i : Fin t => Function.update G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t))
          (Fin.last L, i.castSucc)) = fun i => G (Fin.last L, i.castSucc) :=
        funext fun g => Function.update_of_ne (fun h => (Fin.castSucc_lt_last g).ne (Prod.ext_iff.mp h).2) _ _
      simp only [blockProd, perturb, Function.update_self, Matrix.mul_assoc, e]
    · rw [Function.update_of_ne hℓ]
      congr 1
      funext g
      rw [perturb, Function.update_of_ne]
      intro h
      exact hℓ (Prod.ext_iff.mp h).1
  unfold gateState
  rw [hblk]
  cases L with
  | zero => simp [serialState, Matrix.mulVec_mulVec]
  | succ L =>
    have e : (fun i : Fin (L + 1) => Function.update (fun ℓ => blockProd (t + 1) fun g => G (ℓ, g))
        (Fin.last (L + 1)) (A * blockProd (t + 1) fun g => G (Fin.last (L + 1), g)) i.castSucc) =
        fun i => blockProd (t + 1) fun g => G (i.castSucc, g) :=
      funext fun i => Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
    simp only [serialState, Function.update_self, ← Matrix.mulVec_mulVec, e]

/-- **Corollary 4.5(i), first part.** Moving the last gate along `readoutCurve` has tangent-coefficient function `h = i μ` and
    leaves the output unchanged. -/
theorem gate_readout_rotation (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (x : ℝ) :
    gateH L (t + 1) G (Fin.last L, Fin.last t) (readoutCurve (G (Fin.last L, Fin.last t))) x =
        Complex.I * gateMu L (t + 1) G x ∧
      ∀ s : ℝ, gateModel L (t + 1)
        (perturb G (Fin.last L, Fin.last t) (readoutCurve (G (Fin.last L, Fin.last t)) s)) x =
          gateModel L (t + 1) G x := by
  -- PROVIDED SOLUTION
  -- Write ψ = gateState L (t+1) G x. By `gateState_last_mul` (unfold `readoutCurve`), the perturbed state at `s` is
  -- (cos s • 1 + (I * sin s) • Zm) *ᵥ ψ = (cos s : ℂ) • ψ + (sin s : ℂ) • ((Complex.I • Zm) *ᵥ ψ)
  -- (`Matrix.add_mulVec`, `Matrix.smul_mulVec`, `Matrix.one_mulVec`).
  -- First part: `unfold gateH gateTangent`; by `cos_sin_comb_hasDerivAt` the derivative at 0 is (I • Zm) *ᵥ ψ
  -- (`HasDerivAt.deriv`), and ip (T ψ) ((I • Zm) *ᵥ ψ) = I * ip (T ψ) (Zm *ᵥ ψ) = I * gateMu (ip is linear in its
  -- second argument; `simp [ip, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Zm]`, `ring`).
  -- Second part: `unfold gateModel`, `ip_Zm_re` on both sides. Component 0 of the perturbed state is
  -- (cos s + I sin s) * ψ 0 and component 1 is (cos s − I sin s) * ψ 1; `Complex.normSq_mul`, and
  -- normSq (cos s ± I sin s) = cos² s + sin² s = 1 (`Real.cos_sq_add_sin_sq`).
  have hst : ∀ s : ℝ, gateState L (t + 1)
      (perturb G (Fin.last L, Fin.last t) (readoutCurve (G (Fin.last L, Fin.last t)) s)) x =
      (Real.cos s : ℂ) • gateState L (t + 1) G x +
        (Real.sin s : ℂ) • ((Complex.I • Zm) *ᵥ gateState L (t + 1) G x) := by
    intro s
    unfold readoutCurve
    rw [gateState_last_mul]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_comm]
  refine ⟨?_, fun s => ?_⟩
  · unfold gateH gateTangent
    rw [show (fun s => gateState L (t + 1)
        (perturb G (Fin.last L, Fin.last t) (readoutCurve (G (Fin.last L, Fin.last t)) s)) x) = _ from
      funext hst, (cos_sin_comb_hasDerivAt _ _).deriv]
    unfold gateMu
    simp [ip, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Zm]
    ring
  · unfold gateModel
    rw [hst s, ip_Zm_re, ip_Zm_re]
    have hcs := Real.cos_sq_add_sin_sq s
    simp [Zm, dotProduct, Fin.sum_univ_two, Complex.normSq_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination ((gateState L (t + 1) G x 0).re ^ 2 + (gateState L (t + 1) G x 0).im ^ 2 -
      (gateState L (t + 1) G x 1).re ^ 2 - (gateState L (t + 1) G x 1).im ^ 2) * hcs

/-- **Corollary 4.5(i), second part.** `i μ` lies in the real span `𝒯` of the tangent-coefficient functions. -/
theorem serial_readout_mem_span (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (hG : InSU G) :
    (fun x : ℝ => Complex.I * gateMu L (t + 1) G x) ∈
      Submodule.span ℝ (Set.range (serialTangentFn L (t + 1) G)) := by
  -- PROVIDED SOLUTION
  -- Let i₀ = (Fin.last L, Fin.last t), V = G i₀ ∈ SU(2) and W = Vᴴ * Zm * V, Hermitian (as `conj_herm`, `Zm_hermitian`)
  -- with W 0 0 + W 1 1 = tr W = tr Zm = 0 (`Matrix.trace_mul_cycle`, V * Vᴴ = 1). By `herm_pauli_decomp`,
  -- W = Σ_a (w a : ℂ) • pauli a with real w a. Since V * Vᴴ = 1: Zm * V = V * W, so
  -- (I • Zm) * V = Σ_a (w a : ℂ) • (V * (I • pauli a)).
  -- By `serialTangentFn_eq`, serialTangentFn (L.last, t.last, a) x = ip (T ψ) (gateState (perturb G i₀ (V * (I • pauli a))) x),
  -- and by `gateState_perturb_linear` the state is linear in the replaced gate, so
  -- Σ_a w a • serialTangentFn (L.last, t.last, a) x = ip (T ψ) (gateState (perturb G i₀ ((I • Zm) * V)) x)
  --   = ip (T ψ) ((I • Zm) *ᵥ ψ)   (`gateState_last_mul`)   = I * gateMu …   (as in `gate_readout_rotation`).
  -- Conclude with `Submodule.sum_mem`, `Submodule.smul_mem` and `Submodule.subset_span ⟨_, rfl⟩` (real scalar
  -- multiplication on ℝ → ℂ is pointwise: `Pi.smul_apply`, `Complex.real_smul`).
  set V := G (Fin.last L, Fin.last t) with hVdef
  have h1 : Vᴴ * V = 1 := unitary_star_mul (hG _)
  have h2 : V * Vᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 (hG _).1
  have hS : ∀ (a : Fin 3) (x : ℝ), serialTangentFn L (t + 1) G (Fin.last L, Fin.last t, a) x =
      ip (T (gateState L (t + 1) G x)) ((V * (Complex.I • pauli a) * Vᴴ) *ᵥ gateState L (t + 1) G x) := by
    intro a x
    rw [serialTangentFn_eq, ← gateState_last_mul]
    simp only
    rw [Matrix.mul_assoc _ Vᴴ, h1, Matrix.mul_one]
  set W := Vᴴ * Zm * V with hW
  have hWh : Wᴴ = W := by
    have := conj_herm (D := Vᴴ) Zm_hermitian
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have htr : W 0 0 + W 1 1 = 0 := by
    have : Matrix.trace W = Matrix.trace Zm := by
      rw [hW, Matrix.trace_mul_cycle, h2, Matrix.one_mul]
    rw [Matrix.trace_fin_two] at this
    rw [this]
    simp [Matrix.trace_fin_two, Zm]
  have hdec := herm_pauli_decomp hWh
  rw [htr, zero_div, zero_smul, zero_add] at hdec
  set w : Fin 3 → ℝ := ![(W 0 1).re, -(W 0 1).im, ((W 0 0).re - (W 1 1).re) / 2] with hw
  have hIZ : Complex.I • Zm = ∑ a : Fin 3, ((w a : ℂ)) • (V * (Complex.I • pauli a) * Vᴴ) := by
    have hZ : Zm = V * W * Vᴴ := by
      rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2,
        Matrix.mul_one]
    rw [hZ, hdec, Fin.sum_univ_three]
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_smul, mul_comm Complex.I]
  have hmu : ∀ x, Complex.I * gateMu L (t + 1) G x =
      ip (T (gateState L (t + 1) G x)) ((Complex.I • Zm) *ᵥ gateState L (t + 1) G x) := by
    intro x
    unfold gateMu
    simp [ip, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Zm]
    ring
  have key : (fun x : ℝ => Complex.I * gateMu L (t + 1) G x) =
      ∑ a : Fin 3, w a • serialTangentFn L (t + 1) G (Fin.last L, Fin.last t, a) := by
    funext x
    rw [Finset.sum_apply, hmu x, hIZ]
    simp only [Pi.smul_apply, hS, Complex.real_smul, Fin.sum_univ_three, Matrix.add_mulVec,
      Matrix.smul_mulVec, ip_add_right]
    simp only [ip, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-! ### Corollary 4.5(ii): no spare tangent direction in the serial circuit -/

/-- Every serial tangent-coefficient function is a trigonometric polynomial of degree at most `L`. -/
theorem serial_tangent_coeffs (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    ∃ a : SIdx L tbl → ℤ → ℂ, (∀ j k, k ∉ Finset.Icc (-(L : ℤ)) L → a j k = 0) ∧
      ∀ j x, serialTangentFn L tbl G j x = trig L (a j) x := by
  have hA : ∀ j : SIdx L tbl, ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
      ∀ x, serialTangentFn L tbl G j x = trig L a x := by
    intro j
    obtain ⟨a, ha, haeq⟩ := gate_tangent_trig L tbl G hG (j.1, j.2.1)
      (lieCurve (G (j.1, j.2.1)) (pauli j.2.2))
      (lieCurve_unitary _ _ (hG _).1 (pauli_herm _) (pauli_sq _)) (lieCurve_zero _ _) _
      (lieCurve_hasDerivAt _ _)
    refine ⟨a, fun k hk => ha k fun h => hk ?_, haeq⟩
    have := j.1.isLt
    simp only [Finset.mem_Icc] at h ⊢
    omega
  choose a ha haeq using hA
  exact ⟨a, ha, haeq⟩

/-- `trig` is ℝ-linear in the coefficients, for finite real combinations. -/
theorem trig_real_sum {ι : Type*} [Fintype ι] (L : ℕ) (c : ι → ℝ) (a : ι → ℤ → ℂ) (x : ℝ) :
    trig L (fun k => ∑ j, (c j : ℂ) * a j k) x = ∑ j, (c j : ℂ) * trig L (a j) x := by
  simp only [trig, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The coefficient Jacobian applied to `c` is the real coefficient vector of `2 Re[conj(Σ c_j h_j) μ]`. -/
theorem gateJ_mulVec_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (a : SIdx L tbl → ℤ → ℂ)
    (b : ℤ → ℂ) (ha : ∀ j k, k ∉ Finset.Icc (-(L : ℤ)) L → a j k = 0)
    (hb : ∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0) (hμ : ∀ x, gateMu L tbl G x = trig L b x)
    (haeq : ∀ j x, serialTangentFn L tbl G j x = trig L (a j) x) (c : SIdx L tbl → ℝ) :
    gateJ L tbl G *ᵥ c = realRep L (envCoeff L (fun k => ∑ j, (c j : ℂ) * a j k) b) := by
  funext r
  have hcol : ∀ j, gateJ L tbl G r j = realRep L (envCoeff L (a j) b) r := fun j =>
    congrFun (gateJ_column L tbl G hG j (a j) b (ha j) hb hμ (haeq j)) r
  rw [show envCoeff L (fun k => ∑ j, (c j : ℂ) * a j k) b =
      fun m => ∑ j, (c j : ℂ) * envCoeff L (a j) b m from funext fun m => envCoeff_real_sum L c a b m]
  rw [realRep_real_sum]
  simp only [Matrix.mulVec, dotProduct, hcol]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Corollary 4.5(ii), "if" (every choice of gates).** A real combination of tangent-coefficient functions equal to a
    real multiple of `i μ` lies in the kernel of the coefficient Jacobian. -/
theorem serial_readout_in_kernel (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) (c : SIdx L tbl → ℝ) (lam : ℝ)
    (h : ∀ x, (∑ j, (c j : ℂ) * serialTangentFn L tbl G j x) = (lam : ℂ) * (Complex.I * gateMu L tbl G x)) :
    gateJ L tbl G *ᵥ c = 0 := by
  -- PROVIDED SOLUTION
  -- As in the proof of `gate_coeffJac_factorisation`: `gate_envelope_trig` gives b supported in [−L, L] with
  -- gateMu = trig L b, and `gate_tangent_trig` (with `lieCurve_unitary`, `pauli_herm`, `pauli_sq`, `lieCurve_zero`,
  -- `lieCurve_hasDerivAt`) gives, for every j, a j supported in [−L, L] with serialTangentFn j = trig L (a j);
  -- `gateJ_column` then says column j of gateJ is realRep L (envCoeff L (a j) b).
  -- Put a' k = Σ_j (c j : ℂ) * a j k. Then (gateJ *ᵥ c) r = Σ_j gateJ r j * c j = realRep L (envCoeff L a' b) r
  -- (`Matrix.mulVec`, `dotProduct`, `realRep_real_sum`, `envCoeff_real_sum`).
  -- a' is supported in [−L, L] and trig L a' x = Σ_j c j * trig L (a j) x = lam * I * trig L b x = trig L (fun k => lam * I * b k) x
  -- (hypothesis h; `trig` is linear in the coefficients, `Finset.sum_comm`, `Finset.mul_sum`), so by `trig_coeff_unique`
  -- a' k = lam * I * b k on [−L, L], and outside both sides are 0. Hence a' = fun k => lam * I * b k and
  -- envCoeff L a' b m = Σ_k (conj (lam * I * b k) * b (k + m) + conj (b k) * (lam * I * b (k + m)))
  --                   = Σ_k (−lam * I + lam * I) * conj (b k) * b (k + m) = 0   (`Complex.conj_ofReal`, `Complex.conj_I`).
  -- So realRep L (envCoeff L a' b) = realRep L 0 = 0 (`realRep_congr`, unfold `realRep`).
  obtain ⟨b, hb, hbeq⟩ := gate_envelope_trig L tbl G
  obtain ⟨a, ha, haeq⟩ := serial_tangent_coeffs L tbl G hG
  rw [gateJ_mulVec_eq L tbl G hG a b ha hb hbeq haeq c]
  have ha' : (fun k => ∑ j, (c j : ℂ) * a j k) = fun k => (lam : ℂ) * Complex.I * b k := by
    funext k
    by_cases hk : k ∈ Finset.Icc (-(L : ℤ)) L
    · refine trig_coeff_unique L (fun k => ∑ j, (c j : ℂ) * a j k) (fun k => (lam : ℂ) * Complex.I * b k)
        (fun x => ?_) k hk
      rw [trig_real_sum]
      have e : ∑ j, (c j : ℂ) * trig L (a j) x = ∑ j, (c j : ℂ) * serialTangentFn L tbl G j x := by
        simp only [haeq]
      rw [e, h x, hbeq x]
      simp only [trig, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp [ha _ k hk, hb k hk]
  rw [ha']
  funext r
  have h0 : ∀ m, envCoeff L (fun k => (lam : ℂ) * Complex.I * b k) b m = 0 := by
    intro m
    unfold envCoeff
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [show envCoeff L (fun k => (lam : ℂ) * Complex.I * b k) b = fun _ => 0 from funext h0]
  unfold realRep
  split_ifs <;> simp

/-- Linear algebra behind Corollary 4.5(ii): if `ker Ψ ≤ ker J` and `dim range Ψ = dim range J + 1`, then `Ψ (ker J)` is
    one-dimensional, so it is spanned by any non-zero `Ψ v₀` with `v₀ ∈ ker J`. -/
theorem one_dim_image_of_ker_le {V W U : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
    (Ψ : V →ₗ[ℝ] W) (J : V →ₗ[ℝ] U) (hker : LinearMap.ker Ψ ≤ LinearMap.ker J)
    (hdim : Module.finrank ℝ (LinearMap.range Ψ) = Module.finrank ℝ (LinearMap.range J) + 1)
    (v₀ : V) (hv₀ : J v₀ = 0) (hw : Ψ v₀ ≠ 0) (v : V) (hv : J v = 0) : ∃ lam : ℝ, Ψ v = lam • Ψ v₀ := by
  have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  have hJ := LinearMap.finrank_range_add_finrank_ker J
  have hΨ' := LinearMap.finrank_range_add_finrank_ker (Ψ.domRestrict (LinearMap.ker J))
  have hk : Module.finrank ℝ (LinearMap.ker (Ψ.domRestrict (LinearMap.ker J))) =
      Module.finrank ℝ (LinearMap.ker Ψ) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq
  have h1 : Module.finrank ℝ (LinearMap.range (Ψ.domRestrict (LinearMap.ker J))) = 1 := by omega
  have hmem : ∀ u : V, J u = 0 → Ψ u ∈ LinearMap.range (Ψ.domRestrict (LinearMap.ker J)) := fun u hu =>
    ⟨⟨u, hu⟩, rfl⟩
  have hne : (⟨Ψ v₀, hmem v₀ hv₀⟩ : LinearMap.range (Ψ.domRestrict (LinearMap.ker J))) ≠ 0 := by
    intro h; apply hw; simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨Ψ v, hmem v hv⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Corollary 4.5(ii) at a fixed choice of gates with full-rank coefficient Jacobian and maximal tangent rank. The
    second hypothesis follows from the first: `serial_tangent_rank_of_full_rank`, `serial_no_spare_direction`
    (Section 24). -/
theorem serial_kernel_iff_of_rank (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (hG : InSU G)
    (hJ : 2 * L + 1 ≤ (gateJ L (t + 1) G).rank) (hT : serialTangentRank L (t + 1) G = 2 * (L + 1))
    (c : SIdx L (t + 1) → ℝ) :
    gateJ L (t + 1) G *ᵥ c = 0 ↔ ∃ lam : ℝ, ∀ x, (∑ j, (c j : ℂ) * serialTangentFn L (t + 1) G j x) =
      (lam : ℂ) * (Complex.I * gateMu L (t + 1) G x) := by
  constructor
  swap
  · rintro ⟨lam, h⟩
    exact serial_readout_in_kernel L (t + 1) G hG c lam h
  intro hc
  set Ψ := Fintype.linearCombination ℝ (serialTangentFn L (t + 1) G) with hΨdef
  have hΨ : ∀ c x, Ψ c x = ∑ j, (c j : ℂ) * serialTangentFn L (t + 1) G j x := by
    intro c x
    rw [hΨdef, Fintype.linearCombination_apply, Finset.sum_apply]
    simp [Complex.real_smul]
  set Jl := Matrix.mulVecLin (gateJ L (t + 1) G) with hJl
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Jl := by
    intro c hc0
    rw [LinearMap.mem_ker] at hc0 ⊢
    apply serial_readout_in_kernel L (t + 1) G hG c 0
    intro x
    rw [← hΨ, hc0]
    simp
  have hrange : Module.finrank ℝ (LinearMap.range Ψ) = 2 * (L + 1) := by
    rw [hΨdef, Fintype.range_linearCombination]
    exact hT
  have hJr : Module.finrank ℝ (LinearMap.range Jl) = 2 * L + 1 := by
    have h1 : (gateJ L (t + 1) G).rank = Module.finrank ℝ (LinearMap.range Jl) := rfl
    have h2 := Submodule.finrank_le (LinearMap.range Jl)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, Ψ c₀ = fun x => Complex.I * gateMu L (t + 1) G x := by
    have := serial_readout_mem_span L t G hG
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hc₀J : Jl c₀ = 0 :=
    serial_readout_in_kernel L (t + 1) G hG c₀ 1 (fun x => by rw [← hΨ, hc₀]; simp)
  have hne : Ψ c₀ ≠ 0 := by
    rw [hc₀]
    intro hmu
    have hmu0 : ∀ x, gateMu L (t + 1) G x = trig L (fun _ => 0) x := by
      intro x
      have := congrFun hmu x
      simp only [Pi.zero_apply, mul_eq_zero, Complex.I_ne_zero, false_or] at this
      simp [trig, this]
    obtain ⟨a, ha, haeq⟩ := serial_tangent_coeffs L (t + 1) G hG
    have hJ0 : ∀ c, Jl c = 0 := by
      intro c
      show gateJ L (t + 1) G *ᵥ c = 0
      rw [gateJ_mulVec_eq L (t + 1) G hG a (fun _ => 0) ha (fun _ _ => rfl) hmu0 haeq c]
      funext r
      unfold realRep
      split_ifs <;> simp [envCoeff]
    have : LinearMap.range Jl = ⊥ := by
      rw [LinearMap.range_eq_bot]
      exact LinearMap.ext hJ0
    rw [this, finrank_bot] at hJr
    omega
  obtain ⟨lam, hlam⟩ :=
    one_dim_image_of_ker_le Ψ Jl hker (by rw [hrange, hJr]; ring) c₀ hc₀J hne c hc
  refine ⟨lam, fun x => ?_⟩
  rw [← hΨ, hlam, Pi.smul_apply, hc₀]
  simp [Complex.real_smul]

/-- **Corollary 4.5(ii), "hence at almost every choice".** For almost every choice of gates of the serial circuit, a vector `c` lies in the kernel of the
    coefficient Jacobian `J` if and only if the combination `Σ_j c_j h_j` of tangent-coefficient functions is a real
    multiple of `i μ`, the rotation about the readout axis. -/
theorem serial_no_spare_direction_generic (hFR : FejerRieszHyp) (hQ : GQSPHyp) (hS : SardHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → Fin 2 → Fin 2 → ℂ)) (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      ¬ ∀ c : SIdx L tbl → ℝ,
        (gateJ L tbl (fun i => Matrix.of (G i)) *ᵥ c = 0 ↔
          ∃ lam : ℝ, ∀ x, (∑ j, (c j : ℂ) * serialTangentFn L tbl (fun i => Matrix.of (G i)) j x) =
            (lam : ℂ) * (Complex.I * gateMu L tbl (fun i => Matrix.of (G i)) x))} = 0 := by
  -- PROVIDED SOLUTION
  -- The set is contained in the union of the null sets of `serial_generic_full_rank hFR hQ hS L tbl htbl μ hμ`
  -- (rank gateJ < 2L+1) and `serial_tangent_rank_generic L tbl htbl μ hμ` (serialTangentRank ≠ 2(L+1)); use
  -- `MeasureTheory.measure_mono_null` and `MeasureTheory.measure_union_null`.
  -- So fix G in SU(2)^m with rank gateJ = 2L+1 (it is ≤ 2L+1 by `Matrix.rank_le_card_height`) and
  -- serialTangentRank = 2(L+1), and show the equivalence for every c.
  -- (⇐) is `serial_readout_in_kernel`.
  -- (⇒) Let Ψ : (SIdx L tbl → ℝ) →ₗ[ℝ] (ℝ → ℂ), Ψ c = fun x => Σ_j (c j : ℂ) * serialTangentFn j x. Its range is the span
  -- of the tangent functions (`Submodule.mem_span_range_iff_exists_fun`), of dimension 2L+2. With a j, b as in
  -- `serial_readout_in_kernel`, gateJ *ᵥ c = realRep L (envCoeff L (Σ_j c j • a j) b) and Σ_j c j • a j is determined
  -- by Ψ c (`trig_coeff_unique`), so ker Ψ ≤ ker (Matrix.mulVecLin gateJ). Rank–nullity
  -- (`LinearMap.finrank_range_add_finrank_ker`, `Matrix.rank` = finrank of the range of `mulVecLin`) with
  -- P = card (SIdx L tbl): dim ker gateJ = P − (2L+1) and dim ker Ψ = P − (2L+2), so the image K = Ψ (ker gateJ) has
  -- dimension 1 (restrict Ψ to ker gateJ; its kernel is ker Ψ).
  -- K contains i μ: write tbl = t + 1 (htbl), take c₀ with Ψ c₀ = i μ from `serial_readout_mem_span`, and
  -- `serial_readout_in_kernel` with lam = 1 puts c₀ in ker gateJ. And i μ ≠ 0 as a function: otherwise gateMu = 0, so
  -- b = 0 on [−L, L] (`trig_coeff_unique`), every column realRep L (envCoeff L (a j) b) of gateJ is 0, gateJ = 0,
  -- contradicting rank 2L+1 ≥ 1. A one-dimensional real space containing the non-zero vector i μ is ℝ · i μ
  -- (`finrank_eq_one_iff_of_nonzero'`), so for c ∈ ker gateJ there is lam with Ψ c = lam • (i μ); evaluate at x.
  obtain ⟨t, rfl⟩ : ∃ t, tbl = t + 1 := ⟨tbl - 1, by omega⟩
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
    (serial_generic_full_rank hFR hQ hS L (t + 1) htbl μ hμ) (serial_tangent_rank_generic L (t + 1) htbl μ hμ))
  rintro G ⟨hSU, hne⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_lt, not_not] at hcon
  exact hne fun c => serial_kernel_iff_of_rank L t _ hSU (hcon.1 hSU) (hcon.2 hSU) c

end

end


/-! # Section 24: Corollary 4.5 at every full-rank point and for almost every target; choice of the phase of ψ^⊥;
generality of Definition 3.1; readout rotations and spare tangent directions -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## 24. Results added for the current version of the paper

In this file `L` is the number of encoding layers: the paper's `E` for the serial and the ancilla circuit, and
`E = 2L` for the parallel circuit on two qubits. -/

/-! ### Part A. Corollary 4.5(ii) at every choice of gates with full row rank, and Corollary 4.5(iii) -/

/-- At every choice of gates at which the coefficient Jacobian has full row rank, the serial circuit has exactly
    `2(L+1)` tangent directions (the remark at the end of the proof of Corollary 4.5(ii)). -/
theorem serial_tangent_rank_of_full_rank (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (hG : InSU G)
    (hJ : (gateJ L (t + 1) G).rank = 2 * L + 1) : serialTangentRank L (t + 1) G = 2 * (L + 1) := by
  -- PROVIDED SOLUTION
  -- `≤` is `serial_tangent_rank_le L (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) G hG`.
  -- `≥`: set Ψ := Fintype.linearCombination ℝ (serialTangentFn L (t + 1) G) and
  -- Jl := Matrix.mulVecLin (gateJ L (t + 1) G), as in the proof of `serial_kernel_iff_of_rank`. Copy from that proof:
  --   hker : LinearMap.ker Ψ ≤ LinearMap.ker Jl                     (`serial_readout_in_kernel` with lam = 0),
  --   hJr  : Module.finrank ℝ (LinearMap.range Jl) = 2 * L + 1      (from hJ; `Matrix.rank` is this finrank by `rfl`),
  --   c₀ with Ψ c₀ = fun x => Complex.I * gateMu L (t + 1) G x      (`serial_readout_mem_span`),
  --   hc₀J : Jl c₀ = 0                                              (`serial_readout_in_kernel` with lam = 1),
  --   hne  : Ψ c₀ ≠ 0                                               (otherwise gateMu = 0, then gateJ = 0 and hJr fails;
  --                                                                  that block uses only hJr, not the tangent rank).
  -- So c₀ ∈ ker Jl and c₀ ∉ ker Ψ: ker Ψ < ker Jl, hence finrank (ker Ψ) < finrank (ker Jl)
  -- (`Submodule.finrank_lt_finrank_of_lt`). Rank–nullity for both maps (`LinearMap.finrank_range_add_finrank_ker`) gives
  -- finrank (range Ψ) ≥ finrank (range Jl) + 1 = 2 * L + 2. Finally finrank (range Ψ) = serialTangentRank L (t + 1) G
  -- (`Fintype.range_linearCombination`, unfold `serialTangentRank`).
  refine le_antisymm (serial_tangent_rank_le L (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) G hG) ?_
  set Ψ := Fintype.linearCombination ℝ (serialTangentFn L (t + 1) G) with hΨdef
  have hΨ : ∀ c x, Ψ c x = ∑ j, (c j : ℂ) * serialTangentFn L (t + 1) G j x := by
    intro c x
    rw [hΨdef, Fintype.linearCombination_apply, Finset.sum_apply]
    simp [Complex.real_smul]
  set Jl := Matrix.mulVecLin (gateJ L (t + 1) G) with hJl
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Jl := by
    intro c hc0
    rw [LinearMap.mem_ker] at hc0 ⊢
    apply serial_readout_in_kernel L (t + 1) G hG c 0
    intro x
    rw [← hΨ, hc0]
    simp
  have hJr : Module.finrank ℝ (LinearMap.range Jl) = 2 * L + 1 := hJ
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, Ψ c₀ = fun x => Complex.I * gateMu L (t + 1) G x := by
    have := serial_readout_mem_span L t G hG
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hc₀J : Jl c₀ = 0 :=
    serial_readout_in_kernel L (t + 1) G hG c₀ 1 (fun x => by rw [← hΨ, hc₀]; simp)
  have hne : Ψ c₀ ≠ 0 := by
    rw [hc₀]
    intro hmu
    have hmu0 : ∀ x, gateMu L (t + 1) G x = trig L (fun _ => 0) x := by
      intro x
      have := congrFun hmu x
      simp only [Pi.zero_apply, mul_eq_zero, Complex.I_ne_zero, false_or] at this
      simp [trig, this]
    obtain ⟨a, ha, haeq⟩ := serial_tangent_coeffs L (t + 1) G hG
    have hJ0 : ∀ c, Jl c = 0 := by
      intro c
      show gateJ L (t + 1) G *ᵥ c = 0
      rw [gateJ_mulVec_eq L (t + 1) G hG a (fun _ => 0) ha (fun _ _ => rfl) hmu0 haeq c]
      funext r
      unfold realRep
      split_ifs <;> simp [envCoeff]
    have : LinearMap.range Jl = ⊥ := by
      rw [LinearMap.range_eq_bot]
      exact LinearMap.ext hJ0
    rw [this, finrank_bot] at hJr
    omega
  have hlt : LinearMap.ker Ψ < LinearMap.ker Jl := by
    refine lt_of_le_of_ne hker fun h => hne ?_
    have : c₀ ∈ LinearMap.ker Jl := hc₀J
    rw [← h] at this
    exact this
  have h0 := Submodule.finrank_lt_finrank_of_lt hlt
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 := LinearMap.finrank_range_add_finrank_ker Jl
  have hrange : Module.finrank ℝ (LinearMap.range Ψ) = serialTangentRank L (t + 1) G := by
    rw [hΨdef, Fintype.range_linearCombination]
    rfl
  omega

/-- **Corollary 4.5(ii).** At every choice of gates of the serial circuit at which the coefficient Jacobian `J` has
    full row rank, a vector `c` satisfies `J c = 0` if and only if `Σ_j c_j h_j` is a real multiple of `i μ`: the
    rotation about the readout axis is the only tangent direction that leaves the output unchanged to first order.
    (The "if" part for every choice of gates is `serial_readout_in_kernel`; "hence at almost every choice" is
    `serial_no_spare_direction_generic`.) -/
theorem serial_no_spare_direction (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (hG : InSU G)
    (hJ : (gateJ L (t + 1) G).rank = 2 * L + 1) (c : SIdx L (t + 1) → ℝ) :
    gateJ L (t + 1) G *ᵥ c = 0 ↔ ∃ lam : ℝ, ∀ x, (∑ j, (c j : ℂ) * serialTangentFn L (t + 1) G j x) =
      (lam : ℂ) * (Complex.I * gateMu L (t + 1) G x) := by
  -- PROVIDED SOLUTION
  -- `exact serial_kernel_iff_of_rank L t G hG hJ.ge (serial_tangent_rank_of_full_rank L t G hG hJ) c`.
  exact serial_kernel_iff_of_rank L t G hG hJ.ge (serial_tangent_rank_of_full_rank L t G hG hJ) c

/-- Euler-angle coordinates of the serial circuit on `ℝ^N`, `N` the number of Euler angles (helper for the Sard step
    of Corollary 4.5(iii); the map `eθ` of the proof of `serial_full_rank_witness`). -/
def serialEulerCoord (L tbl : ℕ) : (Fin (Fintype.card (Idx L tbl)) → ℝ) →L[ℝ] Params L tbl :=
  ContinuousLinearMap.pi fun ℓ => ContinuousLinearMap.pi fun t => ContinuousLinearMap.pi fun c =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card (Idx L tbl)) => ℝ)
      (Fintype.equivFin (Idx L tbl) (ℓ, t, c))

theorem serialEulerCoord_apply (L tbl : ℕ) (y : Fin (Fintype.card (Idx L tbl)) → ℝ) (ℓ : Fin (L + 1))
    (t : Fin tbl) (c : Fin 3) : serialEulerCoord L tbl y ℓ t c = y (Fintype.equivFin (Idx L tbl) (ℓ, t, c)) := rfl

/-- Coefficient vector of the serial circuit as a function of the Euler angles (the map `F` of the proof of
    `serial_full_rank_witness`). -/
def serialCoeffMap (L tbl : ℕ) (y : Fin (Fintype.card (Idx L tbl)) → ℝ) : Fin (2 * L + 1) → ℝ :=
  fun r => ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k * model L tbl (serialEulerCoord L tbl y) (eqGrid L 0 k)

theorem serialCoeffMap_contDiff (L tbl : ℕ) : ∀ k : ℕ, ContDiff ℝ k (serialCoeffMap L tbl) := by
  intro k
  rw [contDiff_pi]
  intro r
  exact ContDiff.sum fun m _ => contDiff_const.mul
    (((model_analytic L tbl _).contDiff).comp (serialEulerCoord L tbl).contDiff)

theorem serialCoeffMap_eq (L tbl : ℕ) (y : Fin (Fintype.card (Idx L tbl)) → ℝ) :
    serialCoeffMap L tbl y = gateCoeffVec L tbl (rotGates L tbl (serialEulerCoord L tbl y)) := by
  conv_rhs => rw [vec_eq_design_inv L 0 (gateCoeffVec L tbl (rotGates L tbl (serialEulerCoord L tbl y)))]
  funext r
  simp only [serialCoeffMap, Matrix.mulVec, dotProduct, ← gate_model_eq_design, gateModel_rotGates]

/-- At a regular point of the Euler-angle coefficient map the coefficient Jacobian has full row rank (the last part
    of the proof of `serial_full_rank_witness`). -/
theorem serial_full_rank_of_regular (L tbl : ℕ) (y : Fin (Fintype.card (Idx L tbl)) → ℝ)
    (hy : LinearMap.range (fderiv ℝ (serialCoeffMap L tbl) y :
      (Fin (Fintype.card (Idx L tbl)) → ℝ) →ₗ[ℝ] (Fin (2 * L + 1) → ℝ)) = ⊤) :
    (gateJ L tbl (rotGates L tbl (serialEulerCoord L tbl y))).rank = 2 * L + 1 := by
  classical
  set idx := Fintype.equivFin (Idx L tbl) with hidx
  set eθ := serialEulerCoord L tbl with heθdef
  have heθ : ∀ y ℓ t c, eθ y ℓ t c = y (idx (ℓ, t, c)) := fun _ _ _ _ => rfl
  set Binv := (designMatrix L (eqGrid L 0))⁻¹ with hBinv
  set F := serialCoeffMap L tbl with hFdef
  have hFc := serialCoeffMap_contDiff L tbl
  set θ := eθ y with hθ
  set G := rotGates L tbl θ with hG
  have hdiffF : DifferentiableAt ℝ F y := ((hFc 1).differentiable (by norm_num)) y
  have hcol : ∀ p : Fin (Fintype.card (Idx L tbl)), fderiv ℝ F y (Pi.single p 1) ∈ LinearMap.range (gateJ L tbl G).mulVecLin := by
    intro p
    set ep : Fin (Fintype.card (Idx L tbl)) → ℝ := Pi.single p (1 : ℝ) with hep
    set j := idx.symm p with hj
    set γ := fun s : ℝ => rotGates L tbl (θ + s • dirVec j) (j.1, j.2.1) with hγdef
    set A' : Matrix (Fin 2) (Fin 2) ℂ := fun a b => deriv (fun s => γ s a b) 0 with hA'
    have hγ : ∀ a b, HasDerivAt (fun s => γ s a b) (A' a b) 0 := rotGates_curve_hasDerivAt L tbl θ j
    have hγ0 : γ 0 = G (j.1, j.2.1) := by simp [hγdef, hG]
    have hline : ∀ s : ℝ, eθ (y + s • ep) = θ + s • dirVec j := by
      intro s
      rw [map_add, map_smul]
      funext ℓ t c
      simp only [Pi.add_apply, Pi.smul_apply, heθ, dirVec, hθ]
      congr 2
      by_cases h : (ℓ, t, c) = j
      · rw [if_pos h, hep, Pi.single_apply, if_pos]
        rw [h]
        exact Equiv.apply_symm_apply idx p
      · rw [if_neg h, hep, Pi.single_apply, if_neg]
        intro h'
        apply h
        rw [hj, ← h', Equiv.symm_apply_apply]
    have h1 : HasDerivAt (fun s : ℝ => F (y + s • ep)) (fderiv ℝ F y (ep)) 0 := by
      have hl : HasDerivAt (fun s : ℝ => y + s • ep) (ep) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ep)).const_add y
      have hF' : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • ep) := by
        simpa using hdiffF.hasFDerivAt
      exact hF'.comp_hasDerivAt (0 : ℝ) hl
    have h2 : HasDerivAt (fun s : ℝ => F (y + s • ep)) (gcol L tbl G (j.1, j.2.1) A') 0 := by
      rw [hasDerivAt_pi]
      intro r
      have e : (fun s : ℝ => F (y + s • ep) r) = fun s =>
          ∑ k, Binv r k * gateModel L tbl (perturb G (j.1, j.2.1) (γ s)) (eqGrid L 0 k) := by
        funext s
        simp only [F, serialCoeffMap]
        rw [hline]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← gateModel_rotGates, rotGates_dirVec]
      rw [e]
      exact HasDerivAt.fun_sum fun k _ =>
        (gateModel_curve_hasDerivAt L tbl G _ γ A' hγ0 hγ _).const_mul _
    rw [h1.unique h2]
    apply gcol_mem_range L tbl G _ (rot_mem_SU2 _ _ _).1 A'
    rw [← hγ0]
    exact velocity_antiHerm γ A' hγ (fun s => (rot_mem_SU2 _ _ _).1)
  have htop : LinearMap.range (gateJ L tbl G).mulVecLin = ⊤ := by
    rw [eq_top_iff, ← hy, LinearMap.range_eq_map, ← (Pi.basisFun ℝ (Fin (Fintype.card (Idx L tbl)))).span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    simpa [Pi.basisFun_apply] using hcol p
  rw [Matrix.rank, htop, finrank_top, Module.finrank_fin_fun]

/-- Sard step of Corollary 4.5(iii). The coefficient vectors that are attained at some choice of gates at which the
    coefficient Jacobian does not have full row rank form a Lebesgue-null subset of `ℝ^{2L+1}`. -/
theorem serial_critical_targets_null (hS : SardHyp) (L tbl : ℕ) :
    MeasureTheory.volume {v : Fin (2 * L + 1) → ℝ | ∃ G : Gates L tbl (Fin 2), InSU G ∧
      gateCoeffVec L tbl G = v ∧ (gateJ L tbl G).rank < 2 * L + 1} = 0 := by
  -- PROVIDED SOLUTION
  -- Use the objects of the proof of `serial_full_rank_witness`: N = Fintype.card (Idx L tbl),
  -- idx = Fintype.equivFin (Idx L tbl), the continuous linear map eθ : (Fin N → ℝ) →L[ℝ] Params L tbl with
  -- eθ y ℓ t c = y (idx (ℓ, t, c)), Binv = (designMatrix L (eqGrid L 0))⁻¹ and
  -- F y r = Σ_k Binv r k * model L tbl (eθ y) (eqGrid L 0 k), together with the facts proved there:
  -- hFc : ∀ k, ContDiff ℝ k F, and hFG : ∀ y, F y = gateCoeffVec L tbl (rotGates L tbl (eθ y)).
  -- (They may be turned into top-level definitions and lemmas of this section.)
  -- Step 1, regular points are full-rank points: for every y with
  --   LinearMap.range (fderiv ℝ F y : (Fin N → ℝ) →ₗ[ℝ] (Fin (2 * L + 1) → ℝ)) = ⊤
  -- one has (gateJ L tbl (rotGates L tbl (eθ y))).rank = 2 * L + 1. This is the last part of the proof of
  -- `serial_full_rank_witness`, from `set θ := eθ y` to the end: `hcol` and `htop` use nothing about y except this
  -- hypothesis. State it as a lemma and copy that argument.
  -- Step 2: let v be in the set, with G, hG : InSU G, hv : gateCoeffVec L tbl G = v and hr : rank < 2 * L + 1.
  -- As in `small_coeff_realised`, `choose φ θ' ω hrot using fun i => rot_surjective (G i) (hG i)` gives Euler angles of
  -- every gate, so G = rotGates L tbl θ for θ ℓ t = ![φ (ℓ, t), θ' (ℓ, t), ω (ℓ, t)], and θ = eθ y for
  -- y p = θ (idx.symm p).1 (idx.symm p).2.1 (idx.symm p).2.2 (as in `hball`). Then F y = v by hFG and hv, and y is a
  -- critical point, since otherwise Step 1 contradicts hr. Hence
  --   v ∈ F '' {y | LinearMap.range (fderiv ℝ F y : (Fin N → ℝ) →ₗ[ℝ] (Fin (2 * L + 1) → ℝ)) ≠ ⊤}.
  -- Step 3: `MeasureTheory.measure_mono_null` with `hS N (2 * L + 1) F hFc`.
  refine MeasureTheory.measure_mono_null ?_
    (hS (Fintype.card (Idx L tbl)) (2 * L + 1) (serialCoeffMap L tbl) (serialCoeffMap_contDiff L tbl))
  rintro v ⟨G, hG, hv, hr⟩
  choose φ θ' ω hrot using fun i => rot_surjective (G i) (hG i)
  set θ : Params L tbl := fun ℓ t => ![φ (ℓ, t), θ' (ℓ, t), ω (ℓ, t)] with hθdef
  have hGθ : rotGates L tbl θ = G := by
    funext i
    simp [rotGates, θ, hrot]
  set idx := Fintype.equivFin (Idx L tbl)
  set y : Fin (Fintype.card (Idx L tbl)) → ℝ := fun p => θ (idx.symm p).1 (idx.symm p).2.1 (idx.symm p).2.2
  have hy : serialEulerCoord L tbl y = θ := by
    funext ℓ t c
    simp [serialEulerCoord_apply, y, idx]
  refine ⟨y, ?_, ?_⟩
  · intro hreg
    have := serial_full_rank_of_regular L tbl y hreg
    rw [hy, hGθ] at this
    omega
  · rw [serialCoeffMap_eq, hy, hGθ, hv]

/-- **Corollary 4.5(iii).** For almost every target, Corollary 4.5(ii) applies at every choice of gates that realises
    it. A target `f* ∈ F_E` is identified with its real coefficient vector `v ∈ ℝ^{2L+1}` (Definition 3.2), and
    "almost every" refers to Lebesgue measure on `ℝ^{2L+1}`: the coefficient vectors `v` for which some choice of gates
    with `gateCoeffVec = v` violates the equivalence of Corollary 4.5(ii) form a null set. (The set of all targets is
    not null: it contains a ball, `serial_targets_contain_ball`.) -/
theorem serial_no_spare_direction_target (hS : SardHyp) (L t : ℕ) :
    MeasureTheory.volume {v : Fin (2 * L + 1) → ℝ | ∃ G : Gates L (t + 1) (Fin 2), InSU G ∧
      gateCoeffVec L (t + 1) G = v ∧ ¬ ∀ c : SIdx L (t + 1) → ℝ,
        (gateJ L (t + 1) G *ᵥ c = 0 ↔ ∃ lam : ℝ, ∀ x,
          (∑ j, (c j : ℂ) * serialTangentFn L (t + 1) G j x) =
            (lam : ℂ) * (Complex.I * gateMu L (t + 1) G x))} = 0 := by
  -- PROVIDED SOLUTION
  -- `MeasureTheory.measure_mono_null ?_ (serial_critical_targets_null hS L (t + 1))`. For v in the set, with G, hG, hv
  -- and the failed equivalence: if (gateJ L (t + 1) G).rank = 2 * L + 1, then `serial_no_spare_direction L t G hG`
  -- gives the equivalence for every c, a contradiction. The rank is ≤ 2 * L + 1 (`Matrix.rank_le_card_height`, then
  -- `Fintype.card_fin`), so it is < 2 * L + 1, and v lies in the set of `serial_critical_targets_null`.
  refine MeasureTheory.measure_mono_null ?_ (serial_critical_targets_null hS L (t + 1))
  rintro v ⟨G, hG, hv, hne⟩
  refine ⟨G, hG, hv, ?_⟩
  have hle : (gateJ L (t + 1) G).rank ≤ 2 * L + 1 :=
    (Matrix.rank_le_card_height _).trans (by simp)
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (fun c => serial_no_spare_direction L t G hG h c) hne

/-- The targets of Corollary 4.5(iii) contain a ball of coefficient vectors, so "almost every target" is not vacuous. -/
theorem serial_targets_contain_ball (hFR : FejerRieszHyp) (hQ : GQSPHyp) (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (v : Fin (2 * L + 1) → ℝ) (hv : ‖v‖ < 1 / (2 * (2 * (L : ℝ) + 1))) :
    ∃ G : Gates L tbl (Fin 2), InSU G ∧ gateCoeffVec L tbl G = v := by
  -- PROVIDED SOLUTION
  -- `obtain ⟨θ, hθ⟩ := small_coeff_realised hFR hQ L tbl htbl v hv` and
  -- `exact ⟨rotGates L tbl θ, rotGates_InSU L tbl θ, hθ⟩`.
  obtain ⟨θ, hθ⟩ := small_coeff_realised hFR hQ L tbl htbl v hv
  exact ⟨rotGates L tbl θ, rotGates_InSU L tbl θ, hθ⟩

/-! ### Part B. Statements made in the text of Sections 4.2 and 4.3 -/

/-- Every unit vector orthogonal to a unit vector `ψ ∈ ℂ²` is `a • Tψ` with `|a| = 1`: the vector `ψ^⊥` is fixed up
    to a phase. -/
theorem perp_unit_eq_phase_T (ψ v : Fin 2 → ℂ) (hψ : ip ψ ψ = 1) (hv : ip ψ v = 0) (hv1 : ip v v = 1) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ v = a • T ψ := by
  -- PROVIDED SOLUTION
  -- Take a = ip (T ψ) v. `perp_eq_smul_T ψ v hψ hv : v = ip (T ψ) v • T ψ` is the second part. For the first part
  -- rewrite one occurrence of v in hv1 with it: ip (a • T ψ) (a • T ψ) = conj a * a * ip (T ψ) (T ψ), and
  -- ip (T ψ) (T ψ) = ip ψ ψ = 1 up to the order of the factors (`simp [ip, T]`, `ring`). Alternatively expand everything:
  -- `simp [ip, T, Complex.ext_iff, Complex.normSq_apply] at hψ hv hv1 ⊢` and `nlinarith`.
  obtain ⟨a, ha⟩ : ∃ a, a = ip (T ψ) v := ⟨_, rfl⟩
  have hv' := perp_eq_smul_T ψ v hψ hv
  rw [← ha] at hv'
  refine ⟨a, ?_, hv'⟩
  have hTT : ip (T ψ) (T ψ) = ip ψ ψ := by
    simp [ip, T]
    ring
  have h : ip v v = (starRingEnd ℂ) a * a * ip (T ψ) (T ψ) := by
    rw [hv']
    simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hTT, hψ, mul_one, hv1] at h
  have h2 := Complex.normSq_eq_conj_mul_self (z := a)
  exact_mod_cast (h2.trans h.symm)

/-- **Text after Lemma 4.2.** Replacing `ψ^⊥` by `a • ψ^⊥` with `|a| = 1` changes neither the vector `h · ψ^⊥` of
    Lemma 4.2(i) nor the product `conj(h) μ` of Lemma 4.2(ii). Here `u` stands for `ψ^⊥`, `ip u dψ` for `h` and `ip u w`
    (with `w = Mψ`) for `μ`; the statement is pointwise in `x`, so the phase may depend on `x`. -/
theorem perp_phase_invariant (u dψ w : Fin 2 → ℂ) (a : ℂ) (ha : Complex.normSq a = 1) :
    ip (a • u) dψ • (a • u) = ip u dψ • u ∧
      (starRingEnd ℂ) (ip (a • u) dψ) * ip (a • u) w = (starRingEnd ℂ) (ip u dψ) * ip u w := by
  -- PROVIDED SOLUTION
  -- From ha: `have h1 : (starRingEnd ℂ) a * a = 1` (`Complex.normSq_eq_conj_mul_self`, or `Complex.mul_conj` and
  -- `mul_comm`). Unfold: `simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul]`. First part: `funext i`, then
  -- `simp only [Pi.smul_apply, smul_eq_mul]` and `linear_combination (… ) * h1`. Second part: `map_add`, `map_mul`,
  -- `Complex.conj_conj`, then `linear_combination (… ) * h1`.
  have h1 : (starRingEnd ℂ) a * a = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ha]
    simp
  rw [ip_smul_left', ip_smul_left']
  refine ⟨?_, ?_⟩
  · rw [smul_smul, show (starRingEnd ℂ) a * ip u dψ * a = ip u dψ by linear_combination ip u dψ * h1]
  · rw [map_mul, Complex.conj_conj]
    linear_combination ((starRingEnd ℂ) (ip u dψ) * ip u w) * h1

/-- **Text after Lemma 4.2, geometric reading.** The inequality behind "`μ` is the direction of steepest ascent":
    the derivative `2 Re[conj(h) μ]` of Lemma 4.2(ii) is at most `2 |h| |μ|` for every tangent amplitude `h`, with
    equality when `h` is a non-negative multiple of `μ`. (With `|μ|² = 1 − f²`, `gate_envelope_normSq`. The statement
    is about the two complex numbers only; the Bloch-sphere picture is not formalised.) -/
theorem envelope_steepest_ascent (h μ : ℂ) :
    2 * ((starRingEnd ℂ) h * μ).re ≤ 2 * (‖h‖ * ‖μ‖) ∧
      ∀ t : ℝ, 0 ≤ t → 2 * ((starRingEnd ℂ) ((t : ℂ) * μ) * μ).re = 2 * (‖(t : ℂ) * μ‖ * ‖μ‖) := by
  -- PROVIDED SOLUTION
  -- First part: the real part of a complex number is at most its norm (`Complex.re_le_norm`, in older Mathlib
  -- `Complex.re_le_abs`), and ‖conj h * μ‖ = ‖h‖ * ‖μ‖ (`norm_mul`, `RCLike.norm_conj` or `Complex.norm_conj`).
  -- Second part: conj (t * μ) * μ = t * (conj μ * μ) = t * (Complex.normSq μ : ℂ) (`map_mul`, `Complex.conj_ofReal`,
  -- `Complex.normSq_eq_conj_mul_self`), with real part t * ‖μ‖ * ‖μ‖ (`Complex.normSq_eq_norm_sq`, `sq`); and
  -- ‖(t : ℂ) * μ‖ = t * ‖μ‖ for t ≥ 0 (`norm_mul`, `Complex.norm_real`, `Real.norm_of_nonneg`).
  constructor
  · have := Complex.re_le_norm ((starRingEnd ℂ) h * μ)
    rw [norm_mul, Complex.norm_conj] at this
    linarith
  · intro t ht
    have e : (starRingEnd ℂ) ((t : ℂ) * μ) * μ = ((t * ‖μ‖ ^ 2 : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e, Complex.ofReal_re, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    ring

/-- **Section 4.3, the basis `e_r(x) = U(x)|r⟩` for one qubit.** For every `D ∈ SU(2)` (in particular the serial
    circuit `U(x)`), `D|1⟩ = T (D|0⟩)`: the basis vector used for the tangent count is Lean's `Tψ`, which is `−ψ^⊥` in the
    paper's sign convention (`Tpaper_eq_neg_T`). -/
theorem T_first_column (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    T (D *ᵥ ![1, 0]) = D *ᵥ ![0, 1] := by
  -- PROVIDED SOLUTION
  -- `rw [T_mulVec_SU2 D hD]`, then `congr 1` and `T ![1, 0] = ![0, 1]`: `funext i`, `fin_cases i`, `simp [T]`.
  rw [T_mulVec_SU2 D hD]
  congr 1
  funext i
  fin_cases i <;> simp [T]

/-- **Section 4.3, "for the serial circuit the number of tangent directions is the rank of the matrix `H` of
    Eq. (2)".** If column `j` of `H` holds the real coordinates of the Fourier coefficients of `h_j` (this is how
    `gate_coeffJac_factorisation` produces `H`; `serialTangentFn` is `gateH` along the Lie curve by definition), then
    `dim 𝒯 = rank H`. -/
theorem serial_tangent_rank_eq_rank_H (L tbl : ℕ) (G : Gates L tbl (Fin 2))
    (H : Matrix (Fin (2 * (2 * L + 1))) (SIdx L tbl) ℝ)
    (hH : ∀ j : SIdx L tbl, ∃ a : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → a k = 0) ∧
      (∀ x, serialTangentFn L tbl G j x = trig L a x) ∧ (fun s => H s j) = coeffVec L a) :
    serialTangentRank L tbl G = H.rank := by
  -- PROVIDED SOLUTION
  -- `choose a ha haeq hcol using hH`. Let Ψ = Fintype.linearCombination ℝ (serialTangentFn L tbl G) and
  -- C = Matrix.mulVecLin H, both defined on SIdx L tbl → ℝ. Show LinearMap.ker Ψ = LinearMap.ker C; then rank–nullity
  -- for both (`LinearMap.finrank_range_add_finrank_ker`) gives finrank (range Ψ) = finrank (range C), which is the
  -- claim (`Fintype.range_linearCombination`, unfold `serialTangentRank`; `Matrix.rank` is finrank (range C) by `rfl`).
  -- For c : SIdx L tbl → ℝ put a' k = Σ_j (c j : ℂ) * a j k, supported in [−L, L]. Then
  -- Ψ c x = Σ_j (c j : ℂ) * trig L (a j) x = trig L a' x (`trig_real_sum`), so Ψ c = 0 iff a' k = 0 for all
  -- k ∈ [−L, L] (`trig_coeff_unique` against the zero sequence; outside the band a' is 0 anyway). And
  -- (H *ᵥ c) s = Σ_j H s j * c j = Σ_j coeffVec L (a j) s * c j = coeffVec L a' s (unfold `coeffVec`: real and
  -- imaginary parts of a real combination; `Complex.re_sum`, `Complex.im_sum`, `Complex.re_ofReal_mul`,
  -- `Complex.im_ofReal_mul`), and coeffVec L a' = 0 iff a' k = 0 for all k ∈ [−L, L]: s = 2 * (k + L) gives the real
  -- part and s = 2 * (k + L) + 1 the imaginary part of a' k.
  classical
  choose a ha haeq hcol using hH
  set Ψ := Fintype.linearCombination ℝ (serialTangentFn L tbl G) with hΨdef
  set C := Matrix.mulVecLin H with hC
  have hΨ : ∀ c x, Ψ c x = ∑ j, (c j : ℂ) * serialTangentFn L tbl G j x := by
    intro c x
    rw [hΨdef, Fintype.linearCombination_apply, Finset.sum_apply]
    simp [Complex.real_smul]
  set a' : (SIdx L tbl → ℝ) → ℤ → ℂ := fun c k => ∑ j, (c j : ℂ) * a j k with ha'def
  have ha' : ∀ c k, k ∉ Finset.Icc (-(L : ℤ)) L → a' c k = 0 := by
    intro c k hk
    simp [a', ha _ k hk]
  have hΨa : ∀ c x, Ψ c x = trig L (a' c) x := by
    intro c x
    rw [hΨ, trig_real_sum]
    simp [haeq]
  have hCa : ∀ c, C c = coeffVec L (a' c) := by
    intro c
    funext s
    have hs : ∀ j, H s j = coeffVec L (a j) s := fun j => congrFun (hcol j) s
    simp only [C, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hs, coeffVec, a']
    split_ifs <;> simp [Complex.re_sum, Complex.im_sum, mul_comm]
  have hzero_iff : ∀ b : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-(L : ℤ)) L → b k = 0) →
      ((∀ x, trig L b x = 0) ↔ coeffVec L b = 0) := by
    intro b hb
    have hall : (∀ k, b k = 0) ↔ coeffVec L b = 0 := by
      constructor
      · intro h
        funext s
        simp [coeffVec, h]
      · intro h k
        by_cases hk : k ∈ Finset.Icc (-(L : ℤ)) L
        · rw [Finset.mem_Icc] at hk
          obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = k + L := ⟨(k + L).toNat, by omega⟩
          have hre := congrFun h ⟨2 * m, by omega⟩
          have him := congrFun h ⟨2 * m + 1, by omega⟩
          have e1 : (((2 * m / 2 : ℕ) : ℤ) - L) = k := by
            rw [Nat.mul_div_cancel_left m (by norm_num)]
            omega
          have e2 : ((((2 * m + 1) / 2 : ℕ) : ℤ) - L) = k := by
            rw [show (2 * m + 1) / 2 = m by omega]
            omega
          simp only [coeffVec, Pi.zero_apply] at hre him
          rw [if_pos (by omega), e1] at hre
          rw [if_neg (by omega), e2] at him
          exact Complex.ext hre him
        · exact hb k hk
    rw [← hall]
    constructor
    · intro h k
      by_cases hk : k ∈ Finset.Icc (-(L : ℤ)) L
      · have := trig_coeff_unique L b (fun _ => 0) (fun x => by rw [h x]; simp [trig]) k hk
        exact this
      · exact hb k hk
    · intro h x
      simp [trig, h]
  have hker : LinearMap.ker Ψ = LinearMap.ker C := by
    ext c
    simp only [LinearMap.mem_ker]
    rw [hCa, ← hzero_iff _ (ha' c)]
    constructor
    · intro h x
      rw [← hΨa, h]
      rfl
    · intro h
      funext x
      rw [hΨa, h x]
      rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 := LinearMap.finrank_range_add_finrank_ker C
  rw [hker] at h1
  have hr : Module.finrank ℝ (LinearMap.range Ψ) = serialTangentRank L tbl G := by
    rw [hΨdef, Fintype.range_linearCombination]
    rfl
  have hHr : H.rank = Module.finrank ℝ (LinearMap.range C) := rfl
  omega

/-! ### Part C. Generality of Definition 3.1 (paragraph "Generality of Definition 3.1" of Appendix B)

A circuit with encoding layer `V S(x) V†`, observable `V_M M V_M†` and initial state `V_0 e` and blocks `W` has the
output of the circuit with encoding layer `S(x)`, observable `M`, initial state `e` and the blocks `reframe … W`. The
identity needs no assumption on `V`, `V_M`, `V_0`. For `V`, `V_M`, `V_0` in SU(n) the blocks stay in SU(n), and for
unitary `V`, `V_M`, `V_0` the map `W ↦ reframe … W` is a bijection. `genModel` with the encoding and readout of the
paper is the serial and the ancilla circuit of this file (`gateModel_eq_genModel`, `ancillaGateModel_eq_genModel`).

Not formalised: that every encoding generator and observable with the eigenvalues of ours, and every initial state,
is of this form (spectral theorem); that left and right translations preserve Haar measure (the file has no Haar
measure, see `HaarNullHyp`); the distribution of `reframe` over the first and the last gate of a block of several
gates; and the correspondence of the optimiser runs. -/

/-- The blocks that absorb a change of encoding generator (`V`), observable (`VM`) and initial state (`V0`):
    `VM† W_L V`, `V† W_ℓ V` for `0 < ℓ < L`, and `V† W_0 V0` (for `L = 0`: `VM† W_0 V0`). (Written as `gqspBlocks`.) -/
def reframe {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (V VM V0 : Matrix n n ℂ)
    (W : Fin (L + 1) → Matrix n n ℂ) : Fin (L + 1) → Matrix n n ℂ :=
  fun ℓ => (if ℓ = Fin.last L then star VM else star V) * W ℓ * (if (ℓ : ℕ) = 0 then V0 else V)

/-- State of the reframed circuit. -/
theorem genState_reframe {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (S : ℝ → Matrix n n ℂ)
    (V B V0 : Matrix n n ℂ) (e : n → ℂ) (W : Fin (L + 1) → Matrix n n ℂ) (x : ℝ) :
    genState L S (reframe L V (star B) V0 W) e x =
      B *ᵥ genState L (fun y => V * S y * star V) W (V0 *ᵥ e) x := by
  -- PROVIDED SOLUTION
  -- Induction on L, generalising B and W: `induction L generalizing B with` after `revert W` (the type of W depends
  -- on L), or a recursive proof by pattern matching on L as in `serialState_split`.
  -- L = 0: the only index is 0 = Fin.last 0, so reframe 0 V (star B) V0 W 0 = star (star B) * W 0 * V0 = B * W 0 * V0, and
  -- both sides are B *ᵥ (W 0 *ᵥ (V0 *ᵥ e)) (`genState`, `Matrix.mulVec_mulVec`).
  -- L + 1: `genState (L + 1) S W' e x = W' (Fin.last (L + 1)) *ᵥ (S x *ᵥ genState L S (fun i => W' (Fin.castSucc i)) e x)`.
  -- For W' = reframe (L + 1) V (star B) V0 W: W' (Fin.last (L + 1)) = B * W (Fin.last (L + 1)) * V, because
  -- `((Fin.last (L + 1) : Fin (L + 2)) : ℕ) = L + 1 ≠ 0` (`Fin.val_last`); and
  -- (fun i => W' (Fin.castSucc i)) = reframe L V (star (star V)) V0 (fun i => W (Fin.castSucc i)),
  -- because `Fin.castSucc i ≠ Fin.last (L + 1)` (`Fin.castSucc_lt_last`), `((Fin.castSucc i : Fin (L + 2)) : ℕ) = (i : ℕ)`
  -- (`Fin.coe_castSucc`), and at i = Fin.last L both branches of the left factor are star V (`star_star`).
  -- The induction hypothesis with B := star V gives star V *ᵥ genState L (fun y => V * S y * star V) (fun i => W (Fin.castSucc i)) (V0 *ᵥ e) x.
  -- Collect: B * W_last * V * S x * star V applied to that state, which is the right-hand side (`Matrix.mulVec_mulVec`,
  -- `Matrix.mul_assoc`).
  induction L generalizing B with
  | zero =>
    simp [genState, reframe, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  | succ L ih =>
    have hlast : reframe (L + 1) V (star B) V0 W (Fin.last (L + 1)) = B * W (Fin.last (L + 1)) * V := by
      simp [reframe]
    have hcs : (fun i : Fin (L + 1) => reframe (L + 1) V (star B) V0 W (Fin.castSucc i)) =
        reframe L V (star (star V)) V0 (fun i => W (Fin.castSucc i)) := by
      funext i
      simp only [reframe, star_star, Fin.val_castSucc, (Fin.castSucc_lt_last i).ne, if_false, ite_self]
    show reframe (L + 1) V (star B) V0 W (Fin.last (L + 1)) *ᵥ (S x *ᵥ genState L S
        (fun i => reframe (L + 1) V (star B) V0 W (Fin.castSucc i)) e x) =
      B *ᵥ (W (Fin.last (L + 1)) *ᵥ ((V * S x * star V) *ᵥ
        genState L (fun y => V * S y * star V) (fun i => W (Fin.castSucc i)) (V0 *ᵥ e) x))
    rw [hlast, hcs, ih (star V)]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Generality of Definition 3.1, outputs.** -/
theorem genModel_reframe {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (S : ℝ → Matrix n n ℂ)
    (M V VM V0 : Matrix n n ℂ) (e : n → ℂ) (W : Fin (L + 1) → Matrix n n ℂ) (x : ℝ) :
    genModel L (fun y => V * S y * star V) (VM * M * star VM) (V0 *ᵥ e) W x =
      genModel L S M e (reframe L V VM V0 W) x := by
  -- PROVIDED SOLUTION
  -- `unfold genModel`. By `genState_reframe` with B := star VM (and `star_star`), the state on the right is
  -- star VM *ᵥ φ with φ = genState L (fun y => V * S y * star V) W (V0 *ᵥ e) x. Then
  -- star (star VM *ᵥ φ) ⬝ᵥ (M *ᵥ (star VM *ᵥ φ)) = star φ ⬝ᵥ ((VM * M * star VM) *ᵥ φ)
  -- (`Matrix.star_mulVec`, `Matrix.dotProduct_mulVec`, `Matrix.vecMul_vecMul`, `Matrix.mulVec_mulVec`, `star_star`).
  unfold genModel
  have h := genState_reframe L S V (star VM) V0 e W x
  rw [star_star] at h
  rw [h]
  congr 1
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/-- **Generality of Definition 3.1, the gates stay in SU(n).** -/
theorem reframe_mem_SU {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (V VM V0 : Matrix n n ℂ)
    (hV : V ∈ Matrix.specialUnitaryGroup n ℂ) (hVM : VM ∈ Matrix.specialUnitaryGroup n ℂ)
    (hV0 : V0 ∈ Matrix.specialUnitaryGroup n ℂ) (W : Fin (L + 1) → Matrix n n ℂ)
    (hW : ∀ ℓ, W ℓ ∈ Matrix.specialUnitaryGroup n ℂ) (ℓ : Fin (L + 1)) :
    reframe L V VM V0 W ℓ ∈ Matrix.specialUnitaryGroup n ℂ := by
  -- PROVIDED SOLUTION
  -- `unfold reframe`, `split_ifs`, and in every case `mul_mem (mul_mem _ (hW ℓ)) _`. The star of an element of SU(n)
  -- is in SU(n): `(star (⟨V, hV⟩ : Matrix.specialUnitaryGroup n ℂ)).2`, as in `Kstar_mem_SU2`.
  have hs : ∀ A, A ∈ Matrix.specialUnitaryGroup n ℂ → star A ∈ Matrix.specialUnitaryGroup n ℂ :=
    fun A hA => (star (⟨A, hA⟩ : Matrix.specialUnitaryGroup n ℂ)).2
  unfold reframe
  refine mul_mem (mul_mem ?_ (hW ℓ)) ?_
  · split_ifs
    · exact hs _ hVM
    · exact hs _ hV
  · split_ifs
    · exact hV0
    · exact hV

/-- **Generality of Definition 3.1, bijection.** For unitary `V`, `VM`, `V0` the map `W ↦ reframe L V VM V0 W` has the
    inverse `reframe L (star V) (star VM) (star V0)` (apply the statement to the starred matrices for the other
    composition). -/
theorem reframe_reframe {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ) (V VM V0 : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) (hVM : VM ∈ Matrix.unitaryGroup n ℂ)
    (hV0 : V0 ∈ Matrix.unitaryGroup n ℂ) (W : Fin (L + 1) → Matrix n n ℂ) :
    reframe L (star V) (star VM) (star V0) (reframe L V VM V0 W) = W := by
  -- PROVIDED SOLUTION
  -- `funext ℓ`, `unfold reframe`, `simp only [star_star]`. The goal is
  -- (if ℓ = last then VM else V) * ((if ℓ = last then star VM else star V) * W ℓ * (if (ℓ : ℕ) = 0 then V0 else V)) *
  --   (if (ℓ : ℕ) = 0 then star V0 else star V) = W ℓ.
  -- `split_ifs` and in each case use A * star A = 1 (`Matrix.mem_unitaryGroup_iff`) with `Matrix.mul_assoc`.
  have aux : ∀ A B C D X : Matrix n n ℂ, A * B = 1 → C * D = 1 → A * (B * X * C) * D = X := by
    intro A B C D X h1 h2
    calc A * (B * X * C) * D = (A * B) * X * (C * D) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hV' := Matrix.mem_unitaryGroup_iff.1 hV
  have hVM' := Matrix.mem_unitaryGroup_iff.1 hVM
  have hV0' := Matrix.mem_unitaryGroup_iff.1 hV0
  funext ℓ
  unfold reframe
  simp only [star_star]
  split_ifs <;> exact aux _ _ _ _ _ (by assumption) (by assumption)

/-- The serial circuit of this file is the general circuit of Definition 3.1 (`genModel`, Section 14) with encoding
    `R_X(x)`, readout `Z` and initial state `|0⟩`; so Lemma 4.1 (`coupling_depth`) and the statements of this part apply
    to it. -/
theorem gateModel_eq_genModel (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (x : ℝ) :
    gateModel L tbl G x = genModel L RXm Zm ![1, 0] (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x := by
  -- PROVIDED SOLUTION
  -- `serialState L V x = genState L RXm V ![1, 0] x` for all V, by induction on L (the two recursions are the same;
  -- possibly `rfl` after `induction L`). Then `unfold gateModel gateState genModel` and `ip_eq_dotProduct`.
  have h : ∀ (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ),
      serialState L V x = genState L RXm V ![1, 0] x := by
    intro L
    induction L with
    | zero => intro V; rfl
    | succ L ih => intro V; simp only [serialState, genState, ih]
  unfold gateModel gateState genModel
  rw [h, ip_eq_dotProduct]

/-- The ancilla circuit is the general circuit of Definition 3.1 with encoding `R_X(x) ⊗ I`, readout `I ⊗ Z` and
    initial state `|00⟩`. -/
theorem ancillaGateModel_eq_genModel (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) :
    ancillaGateModel L tbl G x =
      genModel L (fun y => Matrix.kronecker (RXm y) (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm) ket00
        (fun ℓ => blockProd tbl (fun g => G (ℓ, g))) x := by
  -- PROVIDED SOLUTION
  -- `ancillaState L W x = genState L (fun y => Matrix.kronecker (RXm y) 1) W ket00 x` for all W, by induction on L
  -- (same recursion). Then `unfold ancillaGateModel ancillaModel genModel`.
  have h : ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      ancillaState L W x = genState L (fun y => Matrix.kronecker (RXm y) 1) W ket00 x := by
    intro L
    induction L with
    | zero => intro W; rfl
    | succ L ih => intro W; simp only [ancillaState, genState, ih]
  unfold ancillaGateModel ancillaModel genModel
  rw [h]

/-! ### Part D. Readout rotations and spare tangent directions (paragraph "Readout rotations and spare directions" of Appendix B): one qubit and the
ancilla circuit

A tangent direction is a real combination `Σ_j c_j h_j` of tangent-coefficient functions. It leaves the output
unchanged to first order when `J c = 0`. These directions form the space `K = Ψ (ker J)` (`serialUnchanged`,
`ancillaUnchanged`), of dimension `dim 𝒯 − rank J`. The readout rotations form a space `R` of at most one dimension on
one qubit and at most seven on two. The paper calls "spare" every dimension of `K` beyond the readout rotations, that
is `dim K − dim (K ⊓ R)`. Hence: no spare direction in the serial circuit wherever `J` has full row rank (`K = ℝ · i μ`
is the readout rotation, `serialUnchanged_eq_span`), and at least `(6L + 6) − (2L + 1) − 7 = 4L − 2` in the ancilla
circuit wherever its tangent count is at least `6(L + 1)` (`ancilla_spare_ge`, stated without subtraction of natural
numbers as `dim (K ⊓ R) + 4L ≤ dim K + 2`). -/

/-- A traceless Hermitian matrix on one qubit that commutes with the readout `Z` is a real multiple of `Z`: the
    readout rotations of one qubit span one dimension. -/
theorem readout_commutant_one_qubit (Y : Matrix (Fin 2) (Fin 2) ℂ) (hY : Yᴴ = Y) (htr : Y.trace = 0)
    (hc : Y * Zm = Zm * Y) : ∃ w : ℝ, Y = (w : ℂ) • Zm := by
  -- PROVIDED SOLUTION
  -- Entry (0, 1) of hc: −Y 0 1 = Y 0 1, so Y 0 1 = 0; entry (1, 0): Y 1 0 = 0. hY at (0, 0): Y 0 0 is real. htr
  -- (`Matrix.trace_fin_two`): Y 1 1 = −Y 0 0. Take w = (Y 0 0).re and finish with `ext i j`, `fin_cases i`,
  -- `fin_cases j`, `simp [Zm]` (use `Complex.ext_iff`).
  have h01 := congrFun (congrFun hc 0) 1
  have h10 := congrFun (congrFun hc 1) 0
  have h00 := congrFun (congrFun hY 0) 0
  simp [Matrix.mul_apply, Zm, Fin.sum_univ_two] at h01 h10
  rw [Matrix.trace_fin_two] at htr
  simp [Matrix.conjTranspose_apply] at h00
  have h00' : (Y 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp at this
    linarith
  refine ⟨(Y 0 0).re, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Zm]; exact Complex.ext (by simp) (by simp [h00'])
  · simp [Zm]; linear_combination -h01 / 2
  · simp [Zm]; linear_combination h10 / 2
  · simp [Zm]
    have : Y 1 1 = -Y 0 0 := by linear_combination htr
    rw [this]
    exact Complex.ext (by simp) (by simp [h00'])

/-- The seven non-identity two-qubit Pauli words `P ⊗ Q` with `Q ∈ {I, Z}`: `XI, YI, ZI, IZ, XZ, YZ, ZZ`. They are the
    Pauli words that commute with the readout `I ⊗ Z`. -/
def readoutWordIdx : Fin 7 → Fin 4 × Fin 4 := ![(1, 0), (2, 0), (3, 0), (0, 3), (1, 3), (2, 3), (3, 3)]

/-- The same seven words as elements of `PWord`. -/
def readoutWord (t : Fin 7) : PWord := ⟨readoutWordIdx t, by fin_cases t <;> decide⟩

/-- Each of the seven words is Hermitian, traceless and commutes with the readout `I ⊗ Z`. -/
theorem readoutWord_commute (t : Fin 7) :
    (pauliWord (readoutWord t))ᴴ = pauliWord (readoutWord t) ∧ (pauliWord (readoutWord t)).trace = 0 ∧
      pauliWord (readoutWord t) * Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm =
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm * pauliWord (readoutWord t) := by
  -- PROVIDED SOLUTION
  -- `fin_cases t`, then for each word: `pauliWord`, `readoutWord`, `readoutWordIdx`, `pauli1` unfolded; Hermitian by
  -- `Matrix.conjTranspose_kronecker` and `pauli1_herm`; the trace by `Matrix.trace_kronecker` and `pauli1_trace`; the
  -- commutation by `Matrix.mul_kronecker_mul` (both sides are kronecker (pauli1 a) (pauli1 b * Zm) with b ∈ {0, 3},
  -- and pauli1 0 = 1, pauli1 3 = Zm commute with Zm), or entrywise with `ext ⟨a, b⟩ ⟨c, d⟩`, `fin_cases`, `simp`.
  obtain ⟨hH, htr, -, -⟩ := pauliWord_basis_props
  have hH' := hH (Fintype.equivFin PWord (readoutWord t))
  have htr' := htr (Fintype.equivFin PWord (readoutWord t))
  simp only [pauliWordFin, Equiv.symm_apply_apply] at hH' htr'
  refine ⟨hH', htr', ?_⟩
  have hb : pauli1 (readoutWord t).1.2 * Zm = Zm * pauli1 (readoutWord t).1.2 := by
    fin_cases t <;> simp [readoutWord, readoutWordIdx, pauli1, Zm]
  have hK : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B :=
    fun _ _ => rfl
  unfold pauliWord
  rw [hK, hK, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, hb]

/-- The seven words are linearly independent over `ℝ`; with `readout_commutant_two_qubits` and `readoutWord_commute`,
    the traceless Hermitian matrices that commute with `I ⊗ Z` form a real space of dimension exactly seven. -/
theorem readoutWord_linearIndependent :
    LinearIndependent ℝ (fun t : Fin 7 => pauliWord (readoutWord t)) := by
  -- PROVIDED SOLUTION
  -- `Fintype.linearIndependent_iff`: let Σ_t g t • pauliWord (readoutWord t) = 0. Multiply by pauliWord (readoutWord s)
  -- and take the trace: tr(P_s P_t) = 4 if s = t and 0 otherwise (`Matrix.mul_kronecker_mul`, `Matrix.trace_kronecker`,
  -- `pauli1_mul_trace`; the seven index pairs are distinct), so 4 * g s = 0. Or read off seven suitable matrix entries
  -- after `fin_cases`.
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have key : ∀ t, (pauliWord (readoutWord s) * pauliWord (readoutWord t)).trace = if s = t then 4 else 0 := by
    intro t
    have hK : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B :=
      fun _ _ => rfl
    unfold pauliWord
    rw [hK, hK, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, pauli1_mul_trace, pauli1_mul_trace]
    fin_cases s <;> fin_cases t <;> simp [readoutWord, readoutWordIdx] <;> norm_num
  have h := congrArg (fun X => (pauliWord (readoutWord s) * X).trace) hg
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, key, Matrix.mul_zero,
    Matrix.trace_zero] at h
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  have h2 : ((g s : ℂ) * 4) = 0 := by
    rw [← h, Complex.real_smul]
  have : (g s : ℂ) = 0 := by
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · norm_num at h3
  exact_mod_cast this

/-- A traceless Hermitian matrix on two qubits that commutes with the readout `I ⊗ Z` is a real combination of the
    seven words `readoutWord`: the readout rotations of two qubits span at most `2² + 2² − 1 = 7` dimensions. -/
theorem readout_commutant_two_qubits (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hY : Yᴴ = Y)
    (htr : Y.trace = 0)
    (hc : Y * Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm * Y) :
    ∃ w : Fin 7 → ℝ, Y = ∑ t, (w t : ℂ) • pauliWord (readoutWord t) := by
  -- PROVIDED SOLUTION
  -- Entrywise route: entry ((a, b), (c, d)) of hc reads Y (a, b) (c, d) * z d = z b * Y (a, b) (c, d) with z 0 = 1,
  -- z 1 = −1 (`kronZ_mulVec` shows how `kronecker 1 Zm` acts; here use `Matrix.mul_apply`, `Matrix.kronecker`,
  -- `Matrix.kroneckerMap_apply`, `Fintype.sum_prod_type`, `Fin.sum_univ_two`, `Zm`), so Y (a, b) (c, d) = 0 whenever
  -- b ≠ d. hY gives Y p q = conj (Y q p), htr gives Y (0,0) (0,0) + Y (0,1) (0,1) + Y (1,0) (1,0) + Y (1,1) (1,1) = 0.
  -- Take w t = ((pauliWord (readoutWord t) * Y).trace).re / 4, written out with `Fin.sum_univ_seven` (or
  -- `Fin.sum_univ_succ` repeatedly), and check the sixteen entries: `ext ⟨a, b⟩ ⟨c, d⟩`, `fin_cases` on a, b, c, d,
  -- `simp [pauliWord, readoutWord, readoutWordIdx, pauli1, Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.ext_iff]`,
  -- `constructor <;> linarith`.
  -- Trace route: `pauli2_complete Y` writes Y = Σ_q (tr(P_q Y)/4) • P_q over all sixteen words. The coefficients are
  -- real because Y and P_q are Hermitian (as in the proof of `pauliWord_basis_props`); the one of q = (0, 0) is
  -- tr Y / 4 = 0; and for q.2 ∈ {1, 2} the word P_q anticommutes with M = kronecker 1 Zm, so with M * M = 1, hc and
  -- cyclicity of the trace, tr(P_q Y) = tr(P_q Y M M) = tr(P_q M Y M) = −tr(M P_q Y M) = −tr(P_q Y), hence it is 0.
  -- The remaining q are the seven values of `readoutWordIdx`.
  set Mz := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm with hMz
  have hK : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B :=
    fun _ _ => rfl
  have hZZ : Zm * Zm = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Zm]
  have hMM : Mz * Mz = 1 := by
    rw [hMz, hK, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hZZ, Matrix.one_kronecker_one]
  have hanti : ∀ a b : Fin 4, (b = 1 ∨ b = 2) → (Matrix.kronecker (pauli1 a) (pauli1 b) * Y).trace = 0 := by
    intro a b hb
    have hb' : pauli1 b * Zm = (-1 : ℂ) • (Zm * pauli1 b) := by
      rcases hb with rfl | rfl <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1, Zm])
    have hKM : Matrix.kronecker (pauli1 a) (pauli1 b) * Mz =
        (-1 : ℂ) • (Mz * Matrix.kronecker (pauli1 a) (pauli1 b)) := by
      rw [hMz, hK, hK, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb', Matrix.mul_one,
        Matrix.one_mul, Matrix.kronecker_smul]
    set K := Matrix.kronecker (pauli1 a) (pauli1 b)
    have h1 : (K * Y).trace = (K * Mz * Y * Mz).trace := by
      rw [Matrix.mul_assoc K Mz Y, ← hc, show K * (Y * Mz) * Mz = K * Y * (Mz * Mz) by
        simp only [Matrix.mul_assoc], hMM, Matrix.mul_one]
    have h2 : (K * Mz * Y * Mz).trace = -(K * Y).trace := by
      have h3 : (Mz * K * Y * Mz).trace = (K * Y).trace := by
        rw [Matrix.mul_assoc Mz K Y, Matrix.mul_assoc Mz (K * Y) Mz, Matrix.trace_mul_comm Mz,
          Matrix.mul_assoc, hMM, Matrix.mul_one]
      rw [hKM, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, h3]
      simp
    linear_combination (h1.trans h2) / 2
  have h00 : (Matrix.kronecker (pauli1 0) (pauli1 0) * Y).trace = 0 := by
    rw [show pauli1 0 = 1 by simp [pauli1], hK, Matrix.one_kronecker_one, Matrix.one_mul, htr]
  have hreal : ∀ a b : Fin 4, ((((Matrix.kronecker (pauli1 a) (pauli1 b) * Y).trace / 4).re : ℝ) : ℂ) =
      (Matrix.kronecker (pauli1 a) (pauli1 b) * Y).trace / 4 := by
    intro a b
    apply Complex.ext
    · simp
    · have := trace_pw2_herm_im Y hY a b
      simp only [pw2, hK] at this
      simp [this]
  refine ⟨fun t => ((Matrix.kronecker (pauli1 (readoutWordIdx t).1) (pauli1 (readoutWordIdx t).2) * Y).trace
    / 4).re, ?_⟩
  conv_lhs => rw [pauli2_complete Y]
  simp only [hreal]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_seven, readoutWord, readoutWordIdx,
    pauliWord, Matrix.cons_val, h00, hanti _ 1 (Or.inl rfl), hanti _ 2 (Or.inr rfl), zero_div, zero_smul,
    add_zero, zero_add]
  abel

/-- A motion `ψ ↦ e^{isY} ψ` of the final state with `Y` Hermitian and commuting with the Hermitian readout `M` does
    not change the output `⟨ψ, Mψ⟩` to first order: its derivative `2 Re⟨iYψ, Mψ⟩` vanishes. (For `Y` commuting with
    `M` the output is in fact the same for every `s`, since `e^{isY}` commutes with `M`; the matrix exponential is not
    used in this file.) -/
theorem readout_rotation_first_order {n : Type*} [Fintype n] (Y M : Matrix n n ℂ) (hY : Yᴴ = Y) (hM : Mᴴ = M)
    (hc : Y * M = M * Y) (ψ : n → ℂ) : (star ((Complex.I • Y) *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ)).re = 0 := by
  -- PROVIDED SOLUTION
  -- star ((I • Y) *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ) = −I * (star ψ ⬝ᵥ ((Y * M) *ᵥ ψ)) (`Matrix.smul_mulVec`, `star_smul`,
  -- `Matrix.star_mulVec`, `Matrix.dotProduct_mulVec`, hY, `Matrix.mulVec_mulVec`, `Complex.conj_I`).
  -- Y * M is Hermitian: (Y * M)ᴴ = Mᴴ * Yᴴ = M * Y = Y * M. For Hermitian A, z = star ψ ⬝ᵥ (A *ᵥ ψ) satisfies
  -- conj z = z (`Matrix.star_dotProduct`, `Matrix.star_mulVec`, `Matrix.dotProduct_mulVec`), so z.im = 0 and
  -- (−I * z).re = z.im = 0.
  have hYM : (Y * M)ᴴ = Y * M := by rw [Matrix.conjTranspose_mul, hY, hM, hc]
  have e : star ((Complex.I • Y) *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ) = -Complex.I * (star ψ ⬝ᵥ ((Y * M) *ᵥ ψ)) := by
    rw [Matrix.smul_mulVec, star_smul, Matrix.star_mulVec, hY, smul_dotProduct,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    simp
  have hreal : (star ψ ⬝ᵥ ((Y * M) *ᵥ ψ)).im = 0 := by
    have := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Y * M) hYM ψ
    simpa using this
  rw [e]
  simp [hreal]

/-- Linear algebra behind the count of spare directions: if `ker Ψ ≤ ker J`, the image `Ψ (ker J)` has dimension
    `dim range Ψ − dim range J`. -/
theorem unchanged_directions_finrank {V W U : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
    (Ψ : V →ₗ[ℝ] W) (J : V →ₗ[ℝ] U) (hker : LinearMap.ker Ψ ≤ LinearMap.ker J) :
    Module.finrank ℝ (Submodule.map Ψ (LinearMap.ker J)) + Module.finrank ℝ (LinearMap.range J) =
      Module.finrank ℝ (LinearMap.range Ψ) := by
  -- PROVIDED SOLUTION
  -- As in the proof of `one_dim_image_of_ker_le`: rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) for Ψ, for
  -- J and for `Ψ.domRestrict (LinearMap.ker J)`. The range of the restriction is `Submodule.map Ψ (LinearMap.ker J)`
  -- (`LinearMap.range_domRestrict`); its kernel has the dimension of ker Ψ (`LinearMap.ker_domRestrict`,
  -- `(Submodule.comapSubtypeEquivOfLe hker).finrank_eq`). Then `omega`.
  have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  have hJ := LinearMap.finrank_range_add_finrank_ker J
  have hΨ' := LinearMap.finrank_range_add_finrank_ker (Ψ.domRestrict (LinearMap.ker J))
  have hk : Module.finrank ℝ (LinearMap.ker (Ψ.domRestrict (LinearMap.ker J))) =
      Module.finrank ℝ (LinearMap.ker Ψ) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq
  rw [LinearMap.range_domRestrict] at hΨ'
  omega

/-- Serial circuit: the tangent directions that leave the output unchanged to first order, `Ψ (ker J)`. -/
def serialUnchanged (L tbl : ℕ) (G : Gates L tbl (Fin 2)) : Submodule ℝ (ℝ → ℂ) :=
  Submodule.map (Fintype.linearCombination ℝ (serialTangentFn L tbl G))
    (LinearMap.ker (Matrix.mulVecLin (gateJ L tbl G)))

/-- `ker Ψ ≤ ker J` for the serial circuit (helper). -/
theorem serial_tangent_kernel_le (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    LinearMap.ker (Fintype.linearCombination ℝ (serialTangentFn L tbl G)) ≤
      LinearMap.ker (Matrix.mulVecLin (gateJ L tbl G)) := by
  intro c hc0
  rw [LinearMap.mem_ker] at hc0 ⊢
  apply serial_readout_in_kernel L tbl G hG c 0
  intro x
  have := congrFun hc0 x
  rw [Fintype.linearCombination_apply, Finset.sum_apply] at this
  simp only [Pi.smul_apply, Complex.real_smul, Pi.zero_apply] at this
  rw [this]
  simp

/-- Serial circuit: the directions that leave the output unchanged to first order form a space of dimension
    `dim 𝒯 − rank J`, for every choice of gates. -/
theorem serialUnchanged_finrank (L tbl : ℕ) (G : Gates L tbl (Fin 2)) (hG : InSU G) :
    Module.finrank ℝ (serialUnchanged L tbl G) + (gateJ L tbl G).rank = serialTangentRank L tbl G := by
  -- PROVIDED SOLUTION
  -- `unchanged_directions_finrank` with Ψ = Fintype.linearCombination ℝ (serialTangentFn L tbl G) and
  -- J = Matrix.mulVecLin (gateJ L tbl G). hker is the `hker` step of `serial_kernel_iff_of_rank`
  -- (`serial_readout_in_kernel` with lam = 0; it holds for every tbl). `Matrix.rank` is the finrank of the range of
  -- `mulVecLin` by `rfl`, and finrank (range Ψ) = serialTangentRank by `Fintype.range_linearCombination`.
  have h := unchanged_directions_finrank _ _ (serial_tangent_kernel_le L tbl G hG)
  unfold serialTangentRank
  rw [← Fintype.range_linearCombination]
  exact h

/-- **No spare direction in the serial circuit.** At every choice of gates at which `J` has full row rank, the
    directions that leave the output unchanged to first order are exactly the real multiples of `i μ`, the rotation
    about the readout axis: the space has dimension one. -/
theorem serialUnchanged_eq_span (L t : ℕ) (G : Gates L (t + 1) (Fin 2)) (hG : InSU G)
    (hJ : (gateJ L (t + 1) G).rank = 2 * L + 1) :
    serialUnchanged L (t + 1) G =
        Submodule.span ℝ ({fun x : ℝ => Complex.I * gateMu L (t + 1) G x} : Set (ℝ → ℂ)) ∧
      Module.finrank ℝ (serialUnchanged L (t + 1) G) = 1 := by
  -- PROVIDED SOLUTION
  -- Second part: `serialUnchanged_finrank`, `serial_tangent_rank_of_full_rank` and hJ, then `omega`.
  -- First part, `≤`: an element is Ψ c with J c = 0; `serial_no_spare_direction` gives lam with
  -- Ψ c = lam • (fun x => I * gateMu x) (`Fintype.linearCombination_apply`, `Complex.real_smul`, as in `hΨ` of
  -- `serial_kernel_iff_of_rank`), which lies in the span (`Submodule.mem_span_singleton`).
  -- `≥`: `Submodule.span_le`, `Set.singleton_subset_iff`: by `serial_readout_mem_span` there is c₀ with Ψ c₀ = i μ, and
  -- `serial_readout_in_kernel` with lam = 1 gives J c₀ = 0, so i μ ∈ Submodule.map Ψ (ker J).
  have hfr : Module.finrank ℝ (serialUnchanged L (t + 1) G) = 1 := by
    have h1 := serialUnchanged_finrank L (t + 1) G hG
    have h2 := serial_tangent_rank_of_full_rank L t G hG hJ
    omega
  refine ⟨le_antisymm ?_ ?_, hfr⟩
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : gateJ L (t + 1) G *ᵥ c = 0 := hc
    obtain ⟨lam, hlam⟩ := (serial_no_spare_direction L t G hG hJ c).1 hc'
    rw [Submodule.mem_span_singleton]
    refine ⟨lam, ?_⟩
    funext x
    rw [Fintype.linearCombination_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, Complex.real_smul]
    rw [hlam x]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, Fintype.linearCombination ℝ (serialTangentFn L (t + 1) G) c₀ =
        fun x => Complex.I * gateMu L (t + 1) G x := by
      have := serial_readout_mem_span L t G hG
      rw [← Fintype.range_linearCombination] at this
      exact this
    refine ⟨c₀, ?_, hc₀⟩
    show gateJ L (t + 1) G *ᵥ c₀ = 0
    apply serial_readout_in_kernel L (t + 1) G hG c₀ 1
    intro x
    have := congrFun hc₀ x
    rw [Fintype.linearCombination_apply, Finset.sum_apply] at this
    simp only [Pi.smul_apply, Complex.real_smul] at this
    rw [this]
    simp

/-- Envelopes of the ancilla circuit in the basis `U(x)|r⟩`, `r ≠ 00`: `μ_r(x) = ⟨U(x) r, (I ⊗ Z) ψ(x)⟩`. -/
def ancillaMu (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) (r : Fin 3) : ℂ :=
  star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L (ancillaBlocks L tbl G) x)

/-- The ancilla state is the first column of the circuit matrix: `ψ(x) = U(x)|00⟩` (helper). -/
theorem ancillaState_eq_unitary : ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (x : ℝ), ancillaState L W x = ancillaUnitary L W x *ᵥ ket00
  | 0, _, _ => rfl
  | L + 1, W, x => by
    show W (Fin.last (L + 1)) *ᵥ (Matrix.kronecker (RXm x) 1 *ᵥ ancillaState L (fun i => W i.castSucc) x) =
      (W (Fin.last (L + 1)) * (Matrix.kronecker (RXm x) 1 * ancillaUnitary L (fun i => W i.castSucc) x)) *ᵥ
        ket00
    rw [ancillaState_eq_unitary L, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]

/-- The circuit matrix of the ancilla circuit is unitary for unitary blocks (helper). -/
theorem ancillaUnitary_mem : ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    (∀ ℓ, W ℓ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) → ∀ x : ℝ,
    ancillaUnitary L W x ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ
  | 0, _, hW, _ => hW 0
  | L + 1, _, hW, x =>
    mul_mem (hW _) (mul_mem (kron_one_mem_SU4 _ (RXm_mem_SU2 x)).1
      (ancillaUnitary_mem L _ (fun _ => hW _) x))

/-- Expansion of an inner product in the columns of a unitary matrix (helper). -/
theorem dotProduct_unitary_columns {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (u v : ι → ℂ) :
    star u ⬝ᵥ v = ∑ b, (starRingEnd ℂ) (star (fun a => U a b) ⬝ᵥ u) * (star (fun a => U a b) ⬝ᵥ v) := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hcol : ∀ w b, (Uᴴ *ᵥ w) b = star (fun a => U a b) ⬝ᵥ w := by
    intro w b
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have e : star u ⬝ᵥ v = star (Uᴴ *ᵥ u) ⬝ᵥ (Uᴴ *ᵥ v) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [e]
  simp only [dotProduct, Pi.star_apply, hcol]
  rfl

/-- Every one-qubit Pauli matrix squares to the identity (helper). -/
theorem pauli1_mul_self (a : Fin 4) : pauli1 a * pauli1 a = 1 := by
  fin_cases a <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1])

/-- Two-qubit Pauli words are Hermitian (helper). -/
theorem pauliWord_herm (q : PWord) : (pauliWord q)ᴴ = pauliWord q := by
  have := pauliWord_basis_props.1 (Fintype.equivFin PWord q)
  simpa [pauliWordFin] using this

/-- Two-qubit Pauli words square to the identity (helper). -/
theorem pauliWord_mul_self (q : PWord) : pauliWord q * pauliWord q = 1 := by
  have hK : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B :=
    fun _ _ => rfl
  unfold pauliWord
  rw [hK, ← Matrix.mul_kronecker_mul, pauli1_mul_self, pauli1_mul_self, Matrix.one_kronecker_one]

/-- The readout `I ⊗ Z` is Hermitian (helper). -/
theorem kronZ_herm : (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm)ᴴ =
    Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Zm, Matrix.conjTranspose_apply]

/-- Along a Lie coordinate the state of the ancilla circuit moves orthogonally to itself in the real sense:
    `Re ⟨ψ, ψ_j⟩ = 0` (helper). -/
theorem ancilla_cross_re (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (i : Fin (L + 1) × Fin tbl) (q : PWord) (x : ℝ) :
    (star (ancillaState L (ancillaBlocks L tbl G) x) ⬝ᵥ
      ancillaState L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • pauliWord q)))) x).re = 0 := by
  set ψ := ancillaState L (ancillaBlocks L tbl G) x
  set ψq := ancillaState L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • pauliWord q)))) x
  have hconst : ∀ s : ℝ, (star ((Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq) ⬝ᵥ
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ ((Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq))).re
      = 1 := by
    intro s
    have e : (Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq =
        ancillaState L (ancillaBlocks L tbl (perturb G i (lieCurve (G i) (pauliWord q) s))) x := by
      simp only [ψ, ψq]
      unfold ancillaBlocks
      rw [lieCurve_eq_comb, ancillaGateState_perturb_linear, perturb_self]
    have hn := ancillaState_norm L (ancillaBlocks L tbl (perturb G i (lieCurve (G i) (pauliWord q) s)))
      (fun ℓ => perturb_blocks_unitary G hG i _
        (lieCurve_unitary _ _ (hG i).1 (pauliWord_herm q) (pauliWord_mul_self q) s) ℓ) x
    rw [Matrix.one_mulVec, e, hn]
    simp
  have h1 := qform_curve_hasDerivAt (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ψ ψq
  simp_rw [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [Matrix.one_mulVec] at h2
  have h3 : (star ψq ⬝ᵥ ψ).re = (star ψ ⬝ᵥ ψq).re := by
    rw [Matrix.star_dotProduct]
    simp
  linarith

/-- Expansion of the derivative of the ancilla output in the frame `U(x)|r⟩` (helper; the computation behind
    `ancilla_gate_phase_locking`). -/
theorem ancilla_env_expansion (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) (x : ℝ)
    (φ : Fin 2 × Fin 2 → ℂ) (hφ : (star (ancillaState L (ancillaBlocks L tbl G) x) ⬝ᵥ φ).re = 0) :
    (star (ancillaState L (ancillaBlocks L tbl G) x) ⬝ᵥ
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ φ)).re +
      (star φ ⬝ᵥ (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
        ancillaState L (ancillaBlocks L tbl G) x)).re =
    2 * (∑ r, (starRingEnd ℂ) (star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ φ) *
      ancillaMu L tbl G x r).re := by
  set ψ := ancillaState L (ancillaBlocks L tbl G) x with hψ
  set M := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm with hMdef
  set U := ancillaUnitary L (ancillaBlocks L tbl G) x with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    ancillaUnitary_mem L _ (fun ℓ => blockProd_mem (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) tbl _
      (fun g => (hG _).1)) x
  have hM : Mᴴ = M := kronZ_herm
  have hswap : (star ψ ⬝ᵥ (M *ᵥ φ)).re = (star φ ⬝ᵥ (M *ᵥ ψ)).re := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, hM, ← Matrix.dotProduct_mulVec]
    simp
  have hcol0 : (fun a => U a (0, 0)) = ψ := by
    rw [hψ, ancillaState_eq_unitary, ← hUdef]
    funext a
    simp [Matrix.mulVec, dotProduct, ket00]
  have hreal : (star ψ ⬝ᵥ (M *ᵥ ψ)).im = 0 := by
    have := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := M) hM ψ
    simpa using this
  have hexp := dotProduct_unitary_columns U hU φ (M *ᵥ ψ)
  rw [hswap, hexp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, frameIdx, ancillaMu]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [hcol0]
  have h00 : ((starRingEnd ℂ) (star ψ ⬝ᵥ φ) * (star ψ ⬝ᵥ (M *ᵥ ψ))).re = 0 := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hφ, hreal]
    ring
  simp only [Complex.add_re, h00]
  simp only [← hUdef, ← hψ, ← hMdef, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- **Remark 4.3(ii) for the gates of the ancilla circuit.** For every Lie-algebra coordinate `j`,
    `∂_j f = 2 Re Σ_r conj(h_{j,r}) μ_r`, with the three tangent coefficients `h_{j,r}` of Remark 4.3(i) in the basis
    `U(x)|r⟩` (`ancillaTangentFn`) and three envelopes `μ_r` that are the same for all `j`. -/
theorem ancilla_gate_phase_locking (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (j : AIdx L tbl) (x : ℝ) :
    HasDerivAt (fun s => ancillaGateModel L tbl
        (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) x)
      (2 * (∑ r, (starRingEnd ℂ) (ancillaTangentFn L tbl G j x r) * ancillaMu L tbl G x r).re) 0 := by
  -- PROVIDED SOLUTION
  -- Write ψ = ancillaState L (ancillaBlocks L tbl G) x, M = kronecker 1 Zm, U = ancillaUnitary L (ancillaBlocks L tbl G) x
  -- and ψ_j = ancillaState L (ancillaBlocks L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (I • pauliWord j.2.2)))) x.
  -- (1) `ancillaGateModel_lie_hasDerivAt` gives the derivative (star ψ ⬝ᵥ (M *ᵥ ψ_j)).re + (star ψ_j ⬝ᵥ (M *ᵥ ψ)).re,
  --     which is 2 * (star ψ_j ⬝ᵥ (M *ᵥ ψ)).re because M is Hermitian (the two terms are complex conjugates).
  --     (`ancillaBlocks L tbl G` is by definition `fun ℓ => blockProd tbl (fun g => G (ℓ, g))`.)
  -- (2) ψ = U *ᵥ ket00 (induction on L from the definitions of `ancillaState` and `ancillaUnitary`), and U is unitary:
  --     the blocks are unitary (`blockProd_mem`, hG), `kronecker (RXm x) 1` is unitary (`kron_one_mem_SU4`,
  --     `RXm_mem_SU2`), induction on L. So the columns of U are an orthonormal basis: for all u v,
  --     star u ⬝ᵥ v = Σ_b conj (star (fun a => U a b) ⬝ᵥ u) * (star (fun a => U a b) ⬝ᵥ v), from U * star U = 1.
  -- (3) Apply this to u = ψ_j, v = M *ᵥ ψ. The sum over b : Fin 2 × Fin 2 is the term b = (0, 0) plus the three terms
  --     b = frameIdx r (`Fintype.sum_prod_type`, `Fin.sum_univ_two`, `Fin.sum_univ_three`, `frameIdx`).
  --     By `ancillaTangentFn_eq` and the definition of `ancillaMu`, the three terms are
  --     conj (ancillaTangentFn L tbl G j x r) * ancillaMu L tbl G x r.
  --     The term b = (0, 0) is conj (star ψ ⬝ᵥ ψ_j) * (star ψ ⬝ᵥ (M *ᵥ ψ)) and has real part 0: star ψ ⬝ᵥ (M *ᵥ ψ) is real
  --     (M Hermitian) and (star ψ ⬝ᵥ ψ_j).re = 0, because the state along the Lie curve is
  --     (cos s) • ψ + (sin s) • ψ_j (shown in the proof of `ancillaTangentFn_eq`) and has norm one for every s
  --     (`ancillaState_norm` with `perturb_blocks_unitary`, `lieCurve_unitary`, `pauliWord` Hermitian with square 1);
  --     differentiate the norm at s = 0, or subtract the identities for s and −s.
  have h : HasDerivAt (fun s => ancillaGateModel L tbl
        (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) x)
      ((star (ancillaState L (ancillaBlocks L tbl G) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ ancillaState L
            (ancillaBlocks L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x)).re +
        (star (ancillaState L
            (ancillaBlocks L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            ancillaState L (ancillaBlocks L tbl G) x)).re) 0 :=
    ancillaGateModel_lie_hasDerivAt L tbl G (j.1, j.2.1) (pauliWord j.2.2) x
  refine h.congr_deriv ?_
  rw [ancilla_env_expansion L tbl G hG x _ (ancilla_cross_re L tbl G hG (j.1, j.2.1) j.2.2 x)]
  simp only [ancillaTangentFn_eq]

/-- The coefficient Jacobian of the ancilla circuit applied to `c`: the design inverse applied to the derivatives of
    the output along the combined direction `φ = Σ_j c_j ψ_j` (helper). -/
theorem ancillaJ_mulVec (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (c : AIdx L tbl → ℝ)
    (r : Fin (2 * L + 1)) :
    (ancillaJ L tbl G *ᵥ c) r = ∑ k, (designMatrix L (eqGrid L 0))⁻¹ r k *
      ((star (ancillaState L (ancillaBlocks L tbl G) (eqGrid L 0 k)) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            ∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L tbl
              (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) (eqGrid L 0 k))).re +
        (star (∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L tbl
              (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) (eqGrid L 0 k)) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            ancillaState L (ancillaBlocks L tbl G) (eqGrid L 0 k))).re) := by
  show ∑ j, ancillaJ L tbl G r j * c j = _
  simp only [ancillaJ_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : ∀ (a : ℝ) (v : Fin 2 × Fin 2 → ℂ), star ((a : ℂ) • v) = (a : ℂ) • star v := by
    intro a v; rw [star_smul]; simp
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, star_sum, hs,
    sum_dotProduct, smul_dotProduct, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ancillaBlocks
  ring

/-- Ancilla circuit: a combination of tangent-coefficient functions that vanishes identically changes no Fourier
    coefficient to first order (`ker Ψ ≤ ker J`), so `J` factors through the tangent-coefficient functions. -/
theorem ancilla_tangent_kernel_le (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    LinearMap.ker (Fintype.linearCombination ℝ (ancillaTangentFn L tbl G)) ≤
      LinearMap.ker (Matrix.mulVecLin (ancillaJ L tbl G)) := by
  -- PROVIDED SOLUTION
  -- Let c be in the left kernel: for all x and r, Σ_j (c j : ℂ) * ancillaTangentFn L tbl G j x r = 0
  -- (`Fintype.linearCombination_apply`, `Finset.sum_apply`, `Pi.smul_apply`, `Complex.real_smul`).
  -- By `ancillaJ_eq` and `ancillaGateModel_lie_hasDerivAt`, entry (r, j) of ancillaJ is
  -- Σ_k Binv r k * D j k, where D j k is the derivative at s = 0 of the output at x_k = eqGrid L 0 k along coordinate j;
  -- by `ancilla_gate_phase_locking` and uniqueness of the derivative (`HasDerivAt.unique`),
  -- D j k = 2 * (Σ_r' conj (ancillaTangentFn L tbl G j x_k r') * ancillaMu L tbl G x_k r').re.
  -- Then (ancillaJ *ᵥ c) r = Σ_k Binv r k * Σ_j c j * D j k and
  -- Σ_j c j * D j k = 2 * (Σ_r' conj (Σ_j (c j : ℂ) * ancillaTangentFn L tbl G j x_k r') * ancillaMu L tbl G x_k r').re = 0
  -- (`Finset.sum_comm`, `Finset.mul_sum`, `Complex.conj_ofReal`, `map_sum`).
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : ∀ x r, ∑ j, (c j : ℂ) * ancillaTangentFn L tbl G j x r = 0 := by
    intro x r
    have := congrFun (congrFun hc x) r
    rw [Fintype.linearCombination_apply] at this
    simpa [Finset.sum_apply, Complex.real_smul] using this
  funext r
  show (ancillaJ L tbl G *ᵥ c) r = 0
  rw [ancillaJ_mulVec]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hφ : (star (ancillaState L (ancillaBlocks L tbl G) (eqGrid L 0 k)) ⬝ᵥ
      ∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L tbl
        (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) (eqGrid L 0 k)).re = 0 := by
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul,
      ancilla_cross_re L tbl G hG, mul_zero, Finset.sum_const_zero]
  rw [ancilla_env_expansion L tbl G hG _ _ hφ]
  have h0 : ∀ r', star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) (eqGrid L 0 k) a (frameIdx r')) ⬝ᵥ
      ∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L tbl
        (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) (eqGrid L 0 k) = 0 := by
    intro r'
    rw [← hc' (eqGrid L 0 k) r']
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, ancillaTangentFn_eq]
  simp only [h0, map_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re, mul_zero]

/-- Ancilla circuit: the tangent directions that leave the output unchanged to first order, `Ψ (ker J)`. -/
def ancillaUnchanged (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Submodule ℝ (ℝ → Fin 3 → ℂ) :=
  Submodule.map (Fintype.linearCombination ℝ (ancillaTangentFn L tbl G))
    (LinearMap.ker (Matrix.mulVecLin (ancillaJ L tbl G)))

/-- Ancilla circuit: the directions that leave the output unchanged to first order form a space of dimension
    `dim 𝒯 − rank J`, for every choice of gates. -/
theorem ancillaUnchanged_finrank (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    Module.finrank ℝ (ancillaUnchanged L tbl G) + (ancillaJ L tbl G).rank = ancillaTangentRank L tbl G := by
  -- PROVIDED SOLUTION
  -- `unchanged_directions_finrank` with hker := `ancilla_tangent_kernel_le L tbl G hG`; `Matrix.rank` is the
  -- finrank of the range of `mulVecLin` by `rfl`; finrank (range Ψ) = ancillaTangentRank by
  -- `Fintype.range_linearCombination` (unfold `ancillaTangentRank`).
  have h := unchanged_directions_finrank _ _ (ancilla_tangent_kernel_le L tbl G hG)
  unfold ancillaTangentRank
  rw [← Fintype.range_linearCombination]
  exact h

/-- Tangent-coefficient function, in the basis `U(x)|r⟩`, of the motion `ψ ↦ e^{isY} ψ` of the final state of the
    ancilla circuit: `r ↦ ⟨U(x) r, iY ψ(x)⟩`. -/
def ancillaRotationFn (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ → Fin 3 → ℂ :=
  fun x r => star (fun a => ancillaUnitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
    ((Complex.I • Y) *ᵥ ancillaState L (ancillaBlocks L tbl G) x)

/-- The readout rotations of the ancilla circuit: the span of the rotation functions of the seven words. -/
def ancillaRotations (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Submodule ℝ (ℝ → Fin 3 → ℂ) :=
  Submodule.span ℝ (Set.range (fun t : Fin 7 => ancillaRotationFn L tbl G (pauliWord (readoutWord t))))

/-- `Y ↦ ancillaRotationFn L tbl G Y` is real-linear (helper). -/
theorem ancillaRotationFn_sum (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ancillaRotationFn L tbl G (∑ t, (w t : ℂ) • P t) = ∑ t, w t • ancillaRotationFn L tbl G (P t) := by
  funext x r
  simp only [ancillaRotationFn, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, Matrix.sum_mulVec,
    Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The rotation functions of all traceless Hermitian `Y` that commute with the readout span exactly
    `ancillaRotations`. -/
theorem ancilla_readout_rotations_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) :
    Submodule.span ℝ {h : ℝ → Fin 3 → ℂ | ∃ Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      Yᴴ = Y ∧ Y.trace = 0 ∧
      Y * Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm =
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm * Y ∧
      h = ancillaRotationFn L tbl G Y} = ancillaRotations L tbl G := by
  -- PROVIDED SOLUTION
  -- Y ↦ ancillaRotationFn L tbl G Y is ℝ-linear: for real w t,
  -- ancillaRotationFn L tbl G (Σ_t (w t : ℂ) • P t) = Σ_t w t • ancillaRotationFn L tbl G (P t)
  -- (`Matrix.smul_mulVec`, `Matrix.sum_mulVec`, `dotProduct_sum`, `dotProduct_smul`, `Finset.smul_sum`, `Complex.real_smul`).
  -- `≤`: `Submodule.span_le`; an element is ancillaRotationFn L tbl G Y with Y as in `readout_commutant_two_qubits`,
  -- hence a real combination of the seven generators (`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`).
  -- `≥`: `Submodule.span_mono`; each generator is in the set by `readoutWord_commute t`.
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro h ⟨Y, hY, htr, hc, rfl⟩
    obtain ⟨w, rfl⟩ := readout_commutant_two_qubits Y hY htr hc
    rw [ancillaRotationFn_sum]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    obtain ⟨h1, h2, h3⟩ := readoutWord_commute t
    exact ⟨_, h1, h2, h3, rfl⟩

/-- **The readout rotations of the ancilla circuit span at most seven dimensions.** -/
theorem ancillaRotations_finrank_le (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) :
    Module.finrank ℝ (ancillaRotations L tbl G) ≤ 7 := by
  -- PROVIDED SOLUTION
  -- `finrank_range_le_card` for the family indexed by `Fin 7` (`Fintype.card_fin`).
  have := finrank_range_le_card (R := ℝ)
    (fun t : Fin 7 => ancillaRotationFn L tbl G (pauliWord (readoutWord t)))
  simpa using this

/-- Replacing the last gate `V` by `A V` multiplies the state of the ancilla circuit by `A` (helper; the analogue of
    `gateState_last_mul`). -/
theorem ancillaState_last_mul (L t : ℕ) (G : Gates L (t + 1) (Fin 2 × Fin 2))
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    ancillaState L (ancillaBlocks L (t + 1)
        (perturb G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t)))) x =
      A *ᵥ ancillaState L (ancillaBlocks L (t + 1) G) x := by
  have hblk : ancillaBlocks L (t + 1) (perturb G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t))) =
      Function.update (fun ℓ => blockProd (t + 1) (fun g => G (ℓ, g))) (Fin.last L)
        (A * blockProd (t + 1) (fun g => G (Fin.last L, g))) := by
    unfold ancillaBlocks
    funext ℓ
    by_cases hℓ : ℓ = Fin.last L
    · subst hℓ
      rw [Function.update_self]
      have e : (fun i : Fin t => Function.update G (Fin.last L, Fin.last t) (A * G (Fin.last L, Fin.last t))
          (Fin.last L, i.castSucc)) = fun i => G (Fin.last L, i.castSucc) :=
        funext fun g => Function.update_of_ne (fun h => (Fin.castSucc_lt_last g).ne (Prod.ext_iff.mp h).2) _ _
      simp only [blockProd, perturb, Function.update_self, Matrix.mul_assoc, e]
    · rw [Function.update_of_ne hℓ]
      congr 1
      funext g
      rw [perturb, Function.update_of_ne]
      intro h
      exact hℓ (Prod.ext_iff.mp h).1
  rw [hblk]
  unfold ancillaBlocks
  cases L with
  | zero => simp [ancillaState, Matrix.mulVec_mulVec]
  | succ L =>
    have e : (fun i : Fin (L + 1) => Function.update (fun ℓ => blockProd (t + 1) fun g => G (ℓ, g))
        (Fin.last (L + 1)) (A * blockProd (t + 1) fun g => G (Fin.last (L + 1), g)) i.castSucc) =
        fun i => blockProd (t + 1) fun g => G (i.castSucc, g) :=
      funext fun i => Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
    simp only [ancillaState, Function.update_self, ← Matrix.mulVec_mulVec, e]

/-- The readout rotations are tangent directions of the circuit that leave the output unchanged to first order: for
    `Y` commuting with the readout, the motion `ψ ↦ e^{isY} ψ` is the motion `V ↦ e^{isY} V` of the last gate. -/
theorem ancillaRotations_le_unchanged (L t : ℕ) (G : Gates L (t + 1) (Fin 2 × Fin 2)) (hG : InSU G) :
    ancillaRotations L (t + 1) G ≤ ancillaUnchanged L (t + 1) G := by
  -- PROVIDED SOLUTION
  -- `Submodule.span_le`; fix a word P = pauliWord (readoutWord t'), Hermitian, traceless, commuting with M = kronecker 1 Zm
  -- (`readoutWord_commute`). Let i₀ = (Fin.last L, Fin.last t), V = G i₀, ψ = ancillaState L (ancillaBlocks L (t+1) G) x.
  -- (a) Last gate: replacing V by A * V multiplies the state by A (the analogue of `gateState_last_mul` for
  --     `ancillaState` and `ancillaBlocks`; same proof).
  -- (b) W := Vᴴ * P * V is Hermitian and traceless, so W = Σ_q (w q : ℂ) • pauliWord q over the fifteen words q : PWord
  --     with real w q (`pauli2_complete`, coefficients real as in the proof of `pauliWord_basis_props`, the word (0,0)
  --     drops because tr W = tr P = 0). Hence (I • P) * V = Σ_q (w q : ℂ) • (V * (I • pauliWord q)).
  -- (c) By `ancillaTangentFn_eq`, linearity of the state in the last gate (`ancillaGateState_perturb_linear`) and (a),
  --     Σ_q w q • ancillaTangentFn L (t+1) G (Fin.last L, Fin.last t, q) = ancillaRotationFn L (t+1) G P.
  --     So with c the vector that is w q at (Fin.last L, Fin.last t, q) and 0 elsewhere, Ψ c = ancillaRotationFn … P.
  -- (d) ancillaJ *ᵥ c = 0: as in the proof of `ancilla_tangent_kernel_le`, (ancillaJ *ᵥ c) r is a combination of
  --     2 * (Σ_r' conj (Ψ c x_k r') * ancillaMu x_k r').re, and by the expansion in the columns of U (step (2) of
  --     `ancilla_gate_phase_locking`) this is 2 * (star ((I • P) *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ)).re minus the term of the column ψ,
  --     conj (star ψ ⬝ᵥ ((I • P) *ᵥ ψ)) * (star ψ ⬝ᵥ (M *ᵥ ψ)), whose real part is 0 (the first factor is imaginary because
  --     P is Hermitian, the second is real). The first is 0 by `readout_rotation_first_order`.
  rw [ancillaRotations, Submodule.span_le]
  rintro _ ⟨t', rfl⟩
  obtain ⟨hPH, hPtr, hPc⟩ := readoutWord_commute t'
  set P := pauliWord (readoutWord t') with hPdef
  set M := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm with hMdef
  set i₀ : Fin (L + 1) × Fin (t + 1) := (Fin.last L, Fin.last t) with hi₀
  set V := G i₀ with hVdef
  have hV : V ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := (hG i₀).1
  have hVV : V * star V = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hVV' : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  set Q := star V * P * V with hQdef
  have hQH : Qᴴ = Q := by
    rw [hQdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hQtr : Q.trace = 0 := by
    rw [hQdef, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one, hPtr]
  obtain ⟨-, -, -, hdec⟩ := pauliWord_basis_props
  have hQ := hdec Q hQH hQtr
  set e := Fintype.equivFin PWord with he
  set coef : Fin (Fintype.card PWord) → ℝ := fun a =>
    ((pauliWordFin a * Q).trace).re / Fintype.card (Fin 2 × Fin 2) with hcoef
  set c : AIdx L (t + 1) → ℝ := fun j => if j.1 = Fin.last L ∧ j.2.1 = Fin.last t then coef (e j.2.2) else 0
    with hcdef
  have hstate : ∀ x, ∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L (t + 1)
      (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x =
      (Complex.I • P) *ᵥ ancillaState L (ancillaBlocks L (t + 1) G) x := by
    intro x
    set ψ := ancillaState L (ancillaBlocks L (t + 1) G) x with hψ
    have hsum : ∑ j, (c j : ℂ) • ancillaState L (ancillaBlocks L (t + 1)
        (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))) x =
        ∑ q : PWord, (coef (e q) : ℂ) • ancillaState L (ancillaBlocks L (t + 1)
          (perturb G i₀ (V * (Complex.I • pauliWord q)))) x := by
      rw [Fintype.sum_prod_type, Fintype.sum_eq_single (Fin.last L)]
      · rw [Fintype.sum_prod_type, Fintype.sum_eq_single (Fin.last t)]
        · simp [c, hi₀, hVdef]
        · intro g hg
          refine Finset.sum_eq_zero fun q _ => ?_
          simp [c, hg]
      · intro ℓ hℓ
        refine Finset.sum_eq_zero fun g _ => ?_
        simp [c, hℓ]
    have hq : ∀ q : PWord, ancillaState L (ancillaBlocks L (t + 1)
        (perturb G i₀ (V * (Complex.I • pauliWord q)))) x =
        (V * (Complex.I • pauliWord q) * star V) *ᵥ ψ := by
      intro q
      have h := ancillaState_last_mul L t G (V * (Complex.I • pauliWord q) * star V) x
      rw [show V * (Complex.I • pauliWord q) * star V * G (Fin.last L, Fin.last t) =
        V * (Complex.I • pauliWord q) by rw [← hi₀, ← hVdef, Matrix.mul_assoc, hVV', Matrix.mul_one]] at h
      exact h
    have hQ' : Q = ∑ q : PWord, (coef (e q) : ℂ) • pauliWord q := by
      conv_lhs => rw [hQ]
      rw [← e.sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp [pauliWordFin, coef, e]
    have hVQ : V * (Complex.I • Q) * star V = Complex.I • P := by
      rw [hQdef, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [show V * (star V * P * V) * star V = (V * star V) * P * (V * star V) by
        simp only [Matrix.mul_assoc], hVV, Matrix.one_mul, Matrix.mul_one]
    rw [hsum]
    simp only [hq, ← Matrix.smul_mulVec, ← Matrix.sum_mulVec]
    congr 1
    rw [← hVQ, hQ', Finset.smul_sum, Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    exact smul_comm _ _ _
  refine ⟨c, ?_, ?_⟩
  · show ancillaJ L (t + 1) G *ᵥ c = 0
    funext r
    rw [ancillaJ_mulVec]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hstate]
    set ψ := ancillaState L (ancillaBlocks L (t + 1) G) (eqGrid L 0 k)
    have h1 := readout_rotation_first_order P M hPH kronZ_herm hPc ψ
    have h2 : (star ψ ⬝ᵥ (M *ᵥ ((Complex.I • P) *ᵥ ψ))).re = (star ((Complex.I • P) *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ)).re := by
      rw [Matrix.star_dotProduct, Matrix.star_mulVec, kronZ_herm, ← hMdef, ← Matrix.dotProduct_mulVec]
      simp
    rw [h2, h1]
    simp
  · funext x r
    rw [Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, ancillaTangentFn_eq, ancillaRotationFn]
    rw [← hstate x]
    simp only [dotProduct_sum, dotProduct_smul, Complex.real_smul, smul_eq_mul]

/-- **Spare directions of the ancilla circuit, at given gates.** Wherever the tangent count is at least `6(L + 1)`
    (Proposition 4.4(ii)), the directions that leave the output unchanged to first order span at least
    `(6L + 6) − (2L + 1) = 4L + 5` dimensions, of which at most seven are readout rotations: at least `4L − 2` are
    spare, `dim K − dim (K ⊓ R) ≥ 4L − 2`, written without subtraction. -/
theorem ancilla_spare_ge (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (hT : 6 * (L + 1) ≤ ancillaTangentRank L tbl G) :
    Module.finrank ℝ ↥(ancillaUnchanged L tbl G ⊓ ancillaRotations L tbl G) + 4 * L ≤
      Module.finrank ℝ (ancillaUnchanged L tbl G) + 2 := by
  -- PROVIDED SOLUTION
  -- finrank (K ⊓ R) ≤ finrank R ≤ 7 (`Submodule.finrank_mono inf_le_right`, R is finite-dimensional as the span of a
  -- finite family; `ancillaRotations_finrank_le`). `ancillaUnchanged_finrank` with hT and
  -- (ancillaJ L tbl G).rank ≤ 2 * L + 1 (`Matrix.rank_le_card_height`, `Fintype.card_fin`) gives finrank K ≥ 4 * L + 5.
  -- `omega`.
  have h1 := ancillaUnchanged_finrank L tbl G hG
  have h2 : (ancillaJ L tbl G).rank ≤ 2 * L + 1 := (Matrix.rank_le_card_height _).trans (by simp)
  haveI : FiniteDimensional ℝ (ancillaRotations L tbl G) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have h3 : Module.finrank ℝ ↥(ancillaUnchanged L tbl G ⊓ ancillaRotations L tbl G) ≤
      Module.finrank ℝ (ancillaRotations L tbl G) := Submodule.finrank_mono inf_le_right
  have h4 := ancillaRotations_finrank_le L tbl G
  omega

/-- **Spare directions of the ancilla circuit, for almost every choice of gates:** at least `4L − 2 = 4E − 2`. -/
theorem ancilla_spare_generic (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ))
    (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      ¬ (Module.finrank ℝ ↥(ancillaUnchanged L tbl (fun i => Matrix.of (G i)) ⊓
            ancillaRotations L tbl (fun i => Matrix.of (G i))) + 4 * L ≤
          Module.finrank ℝ (ancillaUnchanged L tbl (fun i => Matrix.of (G i))) + 2)} = 0 := by
  -- PROVIDED SOLUTION
  -- `MeasureTheory.measure_mono_null ?_ (ancilla_tangent_rank_generic L tbl htbl μ hμ)`. For G in the set, with hSU:
  -- if 6 * (L + 1) ≤ ancillaTangentRank, `ancilla_spare_ge` (hG := hSU) contradicts the second component; so
  -- ancillaTangentRank < 6 * (L + 1).
  refine MeasureTheory.measure_mono_null ?_ (ancilla_tangent_rank_generic L tbl htbl μ hμ)
  rintro G ⟨hSU, hne⟩
  refine ⟨hSU, ?_⟩
  by_contra hT
  exact hne (ancilla_spare_ge L tbl _ hSU (not_lt.1 hT))

/-! ### Part E (optional). The parallel circuit on two qubits

Both qubits are encoded, the readout is `Z` on qubit 1 as for the ancilla circuit, and `E = 2L`. The file has no
coefficient Jacobian for this circuit, so "leaves the output unchanged to first order" is stated for the derivative
functions `x ↦ ∂_j f(x)` themselves: a direction `c` leaves the output unchanged when `Σ_j c_j ∂_j f` vanishes
identically. These functions are trigonometric polynomials of degree `≤ E`, so they span at most `2E + 1` dimensions,
the number that `rank J ≤ 2E + 1` stands for in the paper. Wherever the tangent count is `5E + 6 = 10L + 6`
(Proposition 4.4(iii)) the unchanged directions then span at least `(5E + 6) − (2E + 1) = 3E + 5 = 6L + 5` dimensions,
and at least `3E − 2 = 6L − 2` of them are spare. -/

/-- Output of the parallel circuit on two qubits with `L + 1` blocks of `tbl` SU(4) gates: `Z` on qubit 1. -/
def parallel2GateModel (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) : ℝ :=
  (star (parallel2State L (ancillaBlocks L tbl G) x) ⬝ᵥ
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ parallel2State L (ancillaBlocks L tbl G) x)).re

/-- `x ↦ ∂_j f(x)` for the Lie-algebra coordinate `j` of the parallel circuit. -/
def parallel2GradFn (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) : ℝ → ℝ :=
  fun x => deriv (fun s => parallel2GateModel L tbl
    (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) x) 0

/-- Envelopes of the parallel circuit in the basis `U(x)|r⟩`, `r ≠ 00`. -/
def parallel2Mu (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (x : ℝ) (r : Fin 3) : ℂ :=
  star (fun a => parallel2Unitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ parallel2State L (ancillaBlocks L tbl G) x)

/-- The state of the parallel circuit is linear in each gate (helper; the first part of the proof of
    `parallel2TangentFn_eq`). -/
theorem parallel2GateState_perturb_linear (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (i : Fin (L + 1) × Fin tbl) (a b : ℂ) (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    parallel2State L (ancillaBlocks L tbl (perturb G i (a • A + b • B))) x =
      a • parallel2State L (ancillaBlocks L tbl (perturb G i A)) x +
        b • parallel2State L (ancillaBlocks L tbl (perturb G i B)) x := by
  obtain ⟨U, D, -, -, hUD⟩ := gate_blocks_update G i
  obtain ⟨Down, -, hDown⟩ := parallel2_update L (ancillaBlocks L tbl G) (par2Blk L tbl G)
    (par2Blk_eq L tbl G) i.1
  have hb : ∀ A, ancillaBlocks L tbl (perturb G i A) =
      Function.update (ancillaBlocks L tbl G) i.1 (U * A * D) := fun A => hUD A
  rw [hb, hb, hb, (hDown _ x).1, (hDown _ x).1, (hDown _ x).1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- Derivative of the parallel output along a Lie coordinate curve, for any gates (the analogue of
    `ancillaGateModel_lie_hasDerivAt`). -/
theorem parallel2GateModel_lie_hasDerivAt (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (i : Fin (L + 1) × Fin tbl) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x : ℝ) :
    HasDerivAt (fun s => parallel2GateModel L tbl (perturb G i (lieCurve (G i) P s)) x)
      ((star (parallel2State L (ancillaBlocks L tbl G) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ parallel2State L
            (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • P)))) x)).re +
        (star (parallel2State L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • P)))) x) ⬝ᵥ
          (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
            parallel2State L (ancillaBlocks L tbl G) x)).re) 0 := by
  -- PROVIDED SOLUTION
  -- As `ancillaGateModel_lie_hasDerivAt`. The parallel state is linear in each gate (first part of the proof of
  -- `parallel2TangentFn_eq`, via `gate_blocks_update` and `parallel2_update`; extract it as a lemma), so by
  -- `lieCurve_eq_comb` and `perturb_self` the state along the curve is
  -- (cos s) • ψ + (sin s) • ψ', ψ' the state with gate i replaced by G i * (I • P). Then `qform_curve_hasDerivAt`.
  have e : ∀ s, parallel2GateModel L tbl (perturb G i (lieCurve (G i) P s)) x =
      (star ((Real.cos s : ℂ) • parallel2State L (ancillaBlocks L tbl G) x +
        (Real.sin s : ℂ) • parallel2State L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • P)))) x) ⬝ᵥ
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
        ((Real.cos s : ℂ) • parallel2State L (ancillaBlocks L tbl G) x +
        (Real.sin s : ℂ) • parallel2State L
          (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • P)))) x))).re := by
    intro s
    unfold parallel2GateModel
    rw [lieCurve_eq_comb, parallel2GateState_perturb_linear, perturb_self]
  simp_rw [e]
  exact qform_curve_hasDerivAt _ _ _

/-- The state of the parallel circuit is the first column of its matrix (helper). -/
theorem parallel2State_eq_unitary : ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (x : ℝ), parallel2State L W x = parallel2Unitary L W x *ᵥ ket00
  | 0, _, _ => rfl
  | L + 1, W, x => by
    show W (Fin.last (L + 1)) *ᵥ (par2Enc x *ᵥ parallel2State L (fun i => W i.castSucc) x) =
      (W (Fin.last (L + 1)) * (par2Enc x * parallel2Unitary L (fun i => W i.castSucc) x)) *ᵥ ket00
    rw [parallel2State_eq_unitary L, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]

/-- The matrix of the parallel circuit is unitary for unitary blocks (helper). -/
theorem parallel2Unitary_mem : ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    (∀ ℓ, W ℓ ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) → ∀ x : ℝ,
    parallel2Unitary L W x ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ
  | 0, _, hW, _ => hW 0
  | L + 1, _, hW, x =>
    mul_mem (hW _) (mul_mem (par2Enc_mem x) (parallel2Unitary_mem L _ (fun _ => hW _) x))

/-- Expansion of the derivative of an output `⟨ψ, (I ⊗ Z) ψ⟩` with `ψ = U|00⟩` in the frame `U|r⟩` (helper; the
    computation of `ancilla_env_expansion` for any unitary `U`). -/
theorem frame_env_expansion (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) (φ : Fin 2 × Fin 2 → ℂ)
    (hφ : (star (U *ᵥ ket00) ⬝ᵥ φ).re = 0) :
    (star (U *ᵥ ket00) ⬝ᵥ (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ φ)).re +
      (star φ ⬝ᵥ (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ (U *ᵥ ket00))).re =
    2 * (∑ r, (starRingEnd ℂ) (star (fun a => U a (frameIdx r)) ⬝ᵥ φ) *
      (star (fun a => U a (frameIdx r)) ⬝ᵥ
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ (U *ᵥ ket00)))).re := by
  set ψ := U *ᵥ ket00 with hψ
  set M := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm with hMdef
  have hM : Mᴴ = M := kronZ_herm
  have hswap : (star ψ ⬝ᵥ (M *ᵥ φ)).re = (star φ ⬝ᵥ (M *ᵥ ψ)).re := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, hM, ← Matrix.dotProduct_mulVec]
    simp
  have hcol0 : (fun a => U a (0, 0)) = ψ := by
    rw [hψ]
    funext a
    simp [Matrix.mulVec, dotProduct, ket00]
  have hreal : (star ψ ⬝ᵥ (M *ᵥ ψ)).im = 0 := by
    have := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := M) hM ψ
    simpa using this
  have hexp := dotProduct_unitary_columns U hU φ (M *ᵥ ψ)
  rw [hswap, hexp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, frameIdx]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [hcol0]
  have h00 : ((starRingEnd ℂ) (star ψ ⬝ᵥ φ) * (star ψ ⬝ᵥ (M *ᵥ ψ))).re = 0 := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hφ, hreal]
    ring
  simp only [Complex.add_re, h00]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- Along a Lie coordinate the state of the parallel circuit moves orthogonally to itself in the real sense
    (helper). -/
theorem parallel2_cross_re (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (i : Fin (L + 1) × Fin tbl) (q : PWord) (x : ℝ) :
    (star (parallel2State L (ancillaBlocks L tbl G) x) ⬝ᵥ
      parallel2State L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • pauliWord q)))) x).re = 0 := by
  set ψ := parallel2State L (ancillaBlocks L tbl G) x
  set ψq := parallel2State L (ancillaBlocks L tbl (perturb G i (G i * (Complex.I • pauliWord q)))) x
  have hconst : ∀ s : ℝ, (star ((Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq) ⬝ᵥ
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ ((Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq))).re
      = 1 := by
    intro s
    have e : (Real.cos s : ℂ) • ψ + (Real.sin s : ℂ) • ψq =
        parallel2State L (ancillaBlocks L tbl (perturb G i (lieCurve (G i) (pauliWord q) s))) x := by
      simp only [ψ, ψq]
      rw [lieCurve_eq_comb, parallel2GateState_perturb_linear, perturb_self]
    have hU := parallel2Unitary_mem L (ancillaBlocks L tbl (perturb G i (lieCurve (G i) (pauliWord q) s)))
      (fun ℓ => perturb_blocks_unitary G hG i _
        (lieCurve_unitary _ _ (hG i).1 (pauliWord_herm q) (pauliWord_mul_self q) s) ℓ) x
    rw [Matrix.one_mulVec, e, parallel2State_eq_unitary, star_mulVec_dotProduct_unitary _ hU]
    simp [dotProduct, ket00]
  have h1 := qform_curve_hasDerivAt (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ψ ψq
  simp_rw [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [Matrix.one_mulVec] at h2
  have h3 : (star ψq ⬝ᵥ ψ).re = (star ψ ⬝ᵥ ψq).re := by
    rw [Matrix.star_dotProduct]
    simp
  linarith

/-- Expansion of the derivative of the parallel output in the frame `U(x)|r⟩` (helper). -/
theorem parallel2_env_expansion (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) (x : ℝ)
    (φ : Fin 2 × Fin 2 → ℂ) (hφ : (star (parallel2State L (ancillaBlocks L tbl G) x) ⬝ᵥ φ).re = 0) :
    (star (parallel2State L (ancillaBlocks L tbl G) x) ⬝ᵥ
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ φ)).re +
      (star φ ⬝ᵥ (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm *ᵥ
        parallel2State L (ancillaBlocks L tbl G) x)).re =
    2 * (∑ r, (starRingEnd ℂ) (star (fun a => parallel2Unitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ φ) *
      parallel2Mu L tbl G x r).re := by
  have hU := parallel2Unitary_mem L (ancillaBlocks L tbl G)
    (fun ℓ => blockProd_mem (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) tbl _ (fun g => (hG _).1)) x
  rw [parallel2State_eq_unitary] at hφ ⊢
  unfold parallel2Mu
  rw [parallel2State_eq_unitary]
  exact frame_env_expansion _ hU φ hφ

/-- **Remark 4.3(ii) for the gates of the parallel circuit.** -/
theorem parallel2_gate_phase_locking (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (j : AIdx L tbl) (x : ℝ) :
    HasDerivAt (fun s => parallel2GateModel L tbl
        (perturb G (j.1, j.2.1) (lieCurve (G (j.1, j.2.1)) (pauliWord j.2.2) s)) x)
      (2 * (∑ r, (starRingEnd ℂ) (parallel2TangentFn L tbl G j x r) * parallel2Mu L tbl G x r).re) 0 := by
  -- PROVIDED SOLUTION
  -- As `ancilla_gate_phase_locking`: start from `parallel2GateModel_lie_hasDerivAt`, rewrite the derivative as
  -- 2 * (star ψ_j ⬝ᵥ (M *ᵥ ψ)).re, and expand in the columns of the unitary U = parallel2Unitary L (ancillaBlocks L tbl G) x
  -- (`par2Enc_mem`; ψ = U *ᵥ ket00), using `parallel2TangentFn_eq`. The column ψ contributes real part 0 because the
  -- state along the Lie curve has norm one.
  refine (parallel2GateModel_lie_hasDerivAt L tbl G (j.1, j.2.1) (pauliWord j.2.2) x).congr_deriv ?_
  rw [parallel2_env_expansion L tbl G hG x _ (parallel2_cross_re L tbl G hG (j.1, j.2.1) j.2.2 x)]
  simp only [parallel2TangentFn_eq]

/-- Every amplitude of the parallel state is a half-integer expansion of degree `2L` (helper). -/
theorem parallel2State_halfExp :
    ∀ (L : ℕ) (W : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p : Fin 2 × Fin 2),
      HalfExp (2 * L) (fun x => parallel2State L W x p)
  | 0, W, p => (HalfExp.const ((W 0 *ᵥ ket00) p)).congr fun _ => rfl
  | L + 1, W, p => by
    have ih := parallel2State_halfExp L (fun i => W (Fin.castSucc i))
    have hin : ∀ q, HalfExp (2 * L + 1 + 1)
        (fun x => (par2Enc x *ᵥ parallel2State L (fun i => W i.castSucc) x) q) := by
      intro q
      refine (HalfExp.sum Finset.univ (fun q' x => RXm x q.1 q'.1 *
        (RXm x q.2 q'.2 * parallel2State L (fun i => W i.castSucc) x q'))
        fun q' _ => ((ih q').RX q.2 q'.2).RX q.1 q'.1).congr fun x => ?_
      simp only [Matrix.mulVec, dotProduct, par2Enc, Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact Finset.sum_congr rfl fun q' _ => by ring
    rw [show 2 * (L + 1) = 2 * L + 1 + 1 by ring]
    exact (HalfExp.sum Finset.univ (fun q x => W (Fin.last (L + 1)) p q *
      (par2Enc x *ᵥ parallel2State L (fun i => W i.castSucc) x) q)
      fun q _ => (hin q).const_mul _).congr fun _ => rfl

/-- A quadratic form between two parallel states is a trigonometric polynomial of degree `2L` (helper). -/
theorem parallel2_qform_trig (L : ℕ) (W W' : Fin (L + 1) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∃ c : ℤ → ℂ, (∀ k, k ∉ Finset.Icc (-((2 * L : ℕ) : ℤ)) ((2 * L : ℕ) : ℤ) → c k = 0) ∧
      ∀ x, star (parallel2State L W x) ⬝ᵥ (K *ᵥ parallel2State L W' x) = trig (2 * L) c x := by
  have hpair : ∀ p : Fin 2 × Fin 2, ∃ a : ℤ → ℂ,
      (∀ k, k ∉ Finset.Icc (-((2 * L : ℕ) : ℤ)) ((2 * L : ℕ) : ℤ) → a k = 0) ∧
      ∀ x, (starRingEnd ℂ) (parallel2State L W x p) * (K *ᵥ parallel2State L W' x) p = trig (2 * L) a x := by
    intro p
    refine (parallel2State_halfExp L W p).pair ?_
    exact (HalfExp.sum Finset.univ (fun q x => K p q * parallel2State L W' x q)
      fun q _ => (parallel2State_halfExp L W' q).const_mul _).congr fun _ => rfl
  choose a ha haeq using hpair
  refine ⟨fun k => ∑ p, a p k, fun k hk => Finset.sum_eq_zero fun p _ => ha p k hk, fun x => ?_⟩
  rw [trig_finset_sum]
  exact Finset.sum_congr rfl fun p _ => haeq p x

/-- Each derivative function of the parallel circuit is a real trigonometric polynomial of degree `2L`, written in
    the design basis (helper). -/
theorem parallel2GradFn_design (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (j : AIdx L tbl) :
    ∃ v : Fin (2 * (2 * L) + 1) → ℝ, ∀ x,
      parallel2GradFn L tbl G j x = ∑ r, designEntry (2 * L) x r * v r := by
  set M := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm with hMdef
  set W := ancillaBlocks L tbl G
  set W' := ancillaBlocks L tbl (perturb G (j.1, j.2.1) (G (j.1, j.2.1) * (Complex.I • pauliWord j.2.2)))
  obtain ⟨c1, hc1, hx1⟩ := parallel2_qform_trig L W W' M
  obtain ⟨c2, hc2, hx2⟩ := parallel2_qform_trig L W' W M
  have hg : ∀ x, parallel2GradFn L tbl G j x =
      (star (parallel2State L W x) ⬝ᵥ (M *ᵥ parallel2State L W' x)).re +
        (star (parallel2State L W' x) ⬝ᵥ (M *ᵥ parallel2State L W x)).re := fun x =>
    (parallel2GateModel_lie_hasDerivAt L tbl G (j.1, j.2.1) (pauliWord j.2.2) x).deriv
  have hBA : ∀ x, star (parallel2State L W' x) ⬝ᵥ (M *ᵥ parallel2State L W x) =
      (starRingEnd ℂ) (star (parallel2State L W x) ⬝ᵥ (M *ᵥ parallel2State L W' x)) := by
    intro x
    rw [← Complex.star_def, Matrix.star_dotProduct, Matrix.star_mulVec, kronZ_herm, ← hMdef,
      ← Matrix.dotProduct_mulVec]
  have hgc : ∀ x, ((parallel2GradFn L tbl G j x : ℝ) : ℂ) = trig (2 * L) (fun k => c1 k + c2 k) x := by
    intro x
    have htr : trig (2 * L) (fun k => c1 k + c2 k) x = trig (2 * L) c1 x + trig (2 * L) c2 x := by
      simp only [trig, add_mul, Finset.sum_add_distrib]
    rw [htr, ← hx1, ← hx2, hg x, hBA x]
    apply Complex.ext <;> simp
  refine ⟨realRep (2 * L) (realFourierCoeff (parallel2GradFn L tbl G j)), fun x => ?_⟩
  refine design_form_of_trig (2 * L) _ (fun k hk => ?_) _ hgc x
  simp [hc1 k hk, hc2 k hk]

/-- The derivative functions `∂_j f` of the parallel circuit are trigonometric polynomials of degree `≤ 2L = E`, so
    they span at most `2E + 1` real dimensions, for every choice of gates. -/
theorem parallel2_grad_span_finrank_le (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (parallel2GradFn L tbl G))) ≤ 2 * (2 * L) + 1 := by
  -- PROVIDED SOLUTION
  -- Every amplitude of `parallel2State L W x` is `HalfExp (2 * L)` in x, for any blocks W: induction on L as in
  -- `ancillaState_halfExp`; an entry of `par2Enc x` is a product of two entries of `RXm x`, so one layer raises the
  -- degree by two (`HalfExp.RX` twice, `HalfExp.sum`, `HalfExp.const_mul`). By `HalfExp.pair`, conj(f) g of two such
  -- amplitudes is `trig (2 * L) a x` with a supported in [−2L, 2L]. By `parallel2GateModel_lie_hasDerivAt` (which
  -- needs no assumption on G) and `HasDerivAt.deriv`, each parallel2GradFn L tbl G j is a real function of the form
  -- x ↦ Σ_r designEntry (2 * L) x r * v r for some v : Fin (2 * (2 * L) + 1) → ℝ (`real_trig_eq_design`, as in
  -- `ancillaModel_trig` and `ancilla_model_eq_design`). So the span is contained in the span of the 2 * (2 * L) + 1
  -- functions x ↦ designEntry (2 * L) x r; `Submodule.finrank_mono` and `finrank_range_le_card`.
  set e : Fin (2 * (2 * L) + 1) → (ℝ → ℝ) := fun r x => designEntry (2 * L) x r with he
  have hle : Submodule.span ℝ (Set.range (parallel2GradFn L tbl G)) ≤ Submodule.span ℝ (Set.range e) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨v, hv⟩ := parallel2GradFn_design L tbl G j
    have h : parallel2GradFn L tbl G j = ∑ r, v r • e r := by
      funext x
      rw [hv]
      simp [e, Finset.sum_apply, mul_comm]
    rw [h]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  calc Module.finrank ℝ (Submodule.span ℝ (Set.range (parallel2GradFn L tbl G)))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range e)) := Submodule.finrank_mono hle
    _ ≤ 2 * (2 * L) + 1 := (finrank_range_le_card (R := ℝ) e).trans (by simp)

/-- Parallel circuit: the tangent directions that leave the output unchanged to first order. -/
def parallel2Unchanged (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Submodule ℝ (ℝ → Fin 3 → ℂ) :=
  Submodule.map (Fintype.linearCombination ℝ (parallel2TangentFn L tbl G))
    (LinearMap.ker (Fintype.linearCombination ℝ (parallel2GradFn L tbl G)))

/-- Parallel circuit: the unchanged directions span at least `dim 𝒯 − (2E + 1)` dimensions, for every choice of
    gates. -/
theorem parallel2Unchanged_finrank_ge (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G) :
    parallel2TangentRank L tbl G ≤ Module.finrank ℝ (parallel2Unchanged L tbl G) + (2 * (2 * L) + 1) := by
  -- PROVIDED SOLUTION
  -- Ψ = Fintype.linearCombination ℝ (parallel2TangentFn L tbl G), Φ = Fintype.linearCombination ℝ (parallel2GradFn L tbl G).
  -- ker Ψ ≤ ker Φ: if Σ_j (c j : ℂ) * parallel2TangentFn L tbl G j x r = 0 for all x, r, then by
  -- `parallel2_gate_phase_locking` (`HasDerivAt.deriv`) Σ_j c j * parallel2GradFn L tbl G j x =
  -- 2 * (Σ_r conj (Σ_j (c j : ℂ) * parallel2TangentFn L tbl G j x r) * parallel2Mu L tbl G x r).re = 0.
  -- `unchanged_directions_finrank` gives finrank (parallel2Unchanged) + finrank (range Φ) = finrank (range Ψ);
  -- finrank (range Ψ) = parallel2TangentRank and finrank (range Φ) ≤ 2 * (2 * L) + 1 by
  -- `Fintype.range_linearCombination` and `parallel2_grad_span_finrank_le`.
  set Ψ := Fintype.linearCombination ℝ (parallel2TangentFn L tbl G) with hΨ
  set Φ := Fintype.linearCombination ℝ (parallel2GradFn L tbl G) with hΦ
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Φ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have hc' : ∀ x r, ∑ j, (c j : ℂ) * parallel2TangentFn L tbl G j x r = 0 := by
      intro x r
      have := congrFun (congrFun hc x) r
      rw [hΨ, Fintype.linearCombination_apply] at this
      simpa [Finset.sum_apply, Complex.real_smul] using this
    funext x
    rw [hΦ, Fintype.linearCombination_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hj : ∀ j, parallel2GradFn L tbl G j x =
        2 * (∑ r, (starRingEnd ℂ) (parallel2TangentFn L tbl G j x r) * parallel2Mu L tbl G x r).re :=
      fun j => (parallel2_gate_phase_locking L tbl G hG j x).deriv
    simp only [hj]
    have h2 : ∑ j, c j * (2 * (∑ r, (starRingEnd ℂ) (parallel2TangentFn L tbl G j x r) *
        parallel2Mu L tbl G x r).re) =
        2 * (∑ r, (starRingEnd ℂ) (∑ j, (c j : ℂ) * parallel2TangentFn L tbl G j x r) *
          parallel2Mu L tbl G x r).re := by
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, Complex.re_ofReal_mul]
      ring
    rw [h2]
    simp [hc']
  have h := unchanged_directions_finrank Ψ Φ hker
  have h2 : Module.finrank ℝ (LinearMap.range Φ) ≤ 2 * (2 * L) + 1 := by
    rw [hΦ, Fintype.range_linearCombination]
    exact parallel2_grad_span_finrank_le L tbl G
  have h3 : Module.finrank ℝ (LinearMap.range Ψ) = parallel2TangentRank L tbl G := by
    rw [hΨ, Fintype.range_linearCombination]
    rfl
  have h4 : Module.finrank ℝ (parallel2Unchanged L tbl G) =
      Module.finrank ℝ (Submodule.map Ψ (LinearMap.ker Φ)) := rfl
  omega

/-- Tangent-coefficient function of the motion `ψ ↦ e^{isY} ψ` of the final state of the parallel circuit. -/
def parallel2RotationFn (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2))
    (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ → Fin 3 → ℂ :=
  fun x r => star (fun a => parallel2Unitary L (ancillaBlocks L tbl G) x a (frameIdx r)) ⬝ᵥ
    ((Complex.I • Y) *ᵥ parallel2State L (ancillaBlocks L tbl G) x)

/-- The readout rotations of the parallel circuit: the span of the rotation functions of the seven words. -/
def parallel2Rotations (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) : Submodule ℝ (ℝ → Fin 3 → ℂ) :=
  Submodule.span ℝ (Set.range (fun t : Fin 7 => parallel2RotationFn L tbl G (pauliWord (readoutWord t))))

/-- `Y ↦ parallel2RotationFn L tbl G Y` is real-linear (helper). -/
theorem parallel2RotationFn_sum (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    parallel2RotationFn L tbl G (∑ t, (w t : ℂ) • P t) = ∑ t, w t • parallel2RotationFn L tbl G (P t) := by
  funext x r
  simp only [parallel2RotationFn, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, Matrix.sum_mulVec,
    Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The rotation functions of all traceless Hermitian `Y` that commute with the readout span exactly
    `parallel2Rotations`, a space of at most seven dimensions. -/
theorem parallel2_readout_rotations_eq (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) :
    Submodule.span ℝ {h : ℝ → Fin 3 → ℂ | ∃ Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      Yᴴ = Y ∧ Y.trace = 0 ∧
      Y * Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm =
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) Zm * Y ∧
      h = parallel2RotationFn L tbl G Y} = parallel2Rotations L tbl G ∧
      Module.finrank ℝ (parallel2Rotations L tbl G) ≤ 7 := by
  -- PROVIDED SOLUTION
  -- As `ancilla_readout_rotations_eq` and `ancillaRotations_finrank_le`.
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro h ⟨Y, hY, htr, hc, rfl⟩
    obtain ⟨w, rfl⟩ := readout_commutant_two_qubits Y hY htr hc
    rw [parallel2RotationFn_sum]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    obtain ⟨h1, h2, h3⟩ := readoutWord_commute t
    exact ⟨_, h1, h2, h3, rfl⟩
  · have := finrank_range_le_card (R := ℝ)
      (fun t : Fin 7 => parallel2RotationFn L tbl G (pauliWord (readoutWord t)))
    simpa using this

/-- **Spare directions of the parallel circuit, at given gates.** Wherever the tangent count is `10L + 6 = 5E + 6`
    (Proposition 4.4(iii)), at least `6L − 2 = 3E − 2` directions are spare: `dim K − dim (K ⊓ R) ≥ 6L − 2`, written
    without subtraction. -/
theorem parallel2_spare_ge (L tbl : ℕ) (G : Gates L tbl (Fin 2 × Fin 2)) (hG : InSU G)
    (hT : parallel2TangentRank L tbl G = 10 * L + 6) :
    Module.finrank ℝ ↥(parallel2Unchanged L tbl G ⊓ parallel2Rotations L tbl G) + 6 * L ≤
      Module.finrank ℝ (parallel2Unchanged L tbl G) + 2 := by
  -- PROVIDED SOLUTION
  -- finrank (K ⊓ R) ≤ finrank R ≤ 7 (`Submodule.finrank_mono inf_le_right`, `parallel2_readout_rotations_eq`);
  -- `parallel2Unchanged_finrank_ge` with hT gives finrank K ≥ 6 * L + 5. `omega`.
  have h1 := parallel2Unchanged_finrank_ge L tbl G hG
  haveI : FiniteDimensional ℝ (parallel2Rotations L tbl G) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have h3 : Module.finrank ℝ ↥(parallel2Unchanged L tbl G ⊓ parallel2Rotations L tbl G) ≤
      Module.finrank ℝ (parallel2Rotations L tbl G) := Submodule.finrank_mono inf_le_right
  have h4 := (parallel2_readout_rotations_eq L tbl G).2
  omega

/-- **Spare directions of the parallel circuit, for almost every choice of gates:** at least `6L − 2 = 3E − 2`. -/
theorem parallel2_spare_generic (L tbl : ℕ) (htbl : 1 ≤ tbl)
    (μ : MeasureTheory.Measure ((Fin (L + 1) × Fin tbl) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ))
    (hμ : HaarNullHyp μ) :
    μ {G | (∀ i, Matrix.of (G i) ∈ Matrix.specialUnitaryGroup (Fin 2 × Fin 2) ℂ) ∧
      ¬ (Module.finrank ℝ ↥(parallel2Unchanged L tbl (fun i => Matrix.of (G i)) ⊓
            parallel2Rotations L tbl (fun i => Matrix.of (G i))) + 6 * L ≤
          Module.finrank ℝ (parallel2Unchanged L tbl (fun i => Matrix.of (G i))) + 2)} = 0 := by
  -- PROVIDED SOLUTION
  -- `MeasureTheory.measure_mono_null ?_ (parallel2_tangent_rank_generic L tbl htbl μ hμ)`. For G in the set with hSU:
  -- if parallel2TangentRank = 10 * L + 6, `parallel2_spare_ge` contradicts the second component; so the rank is
  -- ≠ 10 * L + 6.
  refine MeasureTheory.measure_mono_null ?_ (parallel2_tangent_rank_generic L tbl htbl μ hμ)
  rintro G ⟨hSU, hne⟩
  exact ⟨hSU, fun hT => hne (parallel2_spare_ge L tbl _ hSU hT)⟩

end

end


/-! # Section 25: Theorem 3 of Motlagh and Wiebe (2024) in their own convention (Lemma 3.3(i), proof)

The proof of Lemma 3.3(i) cites generalised quantum signal processing in the convention of Motlagh and Wiebe: rotations in
U(2), the signal `diag(e^{ix}, 1)`, and no global phase. `GQSPHypMW` states that form. `gqspHyp_of_MW` derives from it the
hypothesis `GQSPHyp` of Section 12 (rotations in SU(2), the signal `diag(1, e^{ix})`, a constant global phase), by the two
conversions of the proof: `diag(e^{ix}, 1) = −(iX) diag(1, e^{ix}) (iX)` with `iX ∈ SU(2)`, and every element of U(2) is a
constant phase times an element of SU(2). Every theorem of this file that assumes `GQSPHyp` therefore holds under
`GQSPHypMW`, which is the cited theorem itself. -/

@[expose] public section

open Matrix

open Filter Topology MeasureTheory

set_option autoImplicit false

noncomputable section

/-- Signal operator `diag(e^{ix}, 1)` of Motlagh and Wiebe. -/
def sigMatMW (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.exp (Complex.I * (x : ℂ)), 0; 0, 1]

/-- `U_L diag(e^{ix}, 1) U_{L−1} ⋯ diag(e^{ix}, 1) U_0 e₀`. -/
def sigStateMW : (L : ℕ) → (Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) → ℝ → Fin 2 → ℂ
  | 0, U, _ => U 0 *ᵥ ![1, 0]
  | L + 1, U, x => U (Fin.last (L + 1)) *ᵥ (sigMatMW x *ᵥ sigStateMW L (fun i => U (Fin.castSucc i)) x)

/-- **Cited result.** Theorem 3 of Motlagh and Wiebe (2024), in their convention: every pair of polynomials `p, q` of degree
    `≤ L` in `e^{ix}` with `|p|² + |q|² = 1` on the circle is the first column of a sequence of `L + 1` elements of U(2)
    interleaved with `L` copies of the signal `diag(e^{ix}, 1)`. (Their theorem gives the elements of U(2) in a specific
    parameterisation; only their unitarity is used here.) -/
def GQSPHypMW : Prop :=
  ∀ (L : ℕ) (p q : ℤ → ℂ), (∀ k, k ∉ Finset.Icc (0 : ℤ) L → p k = 0) →
    (∀ k, k ∉ Finset.Icc (0 : ℤ) L → q k = 0) →
    (∀ x, Complex.normSq (trig L p x) + Complex.normSq (trig L q x) = 1) →
    ∃ U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ, (∀ ℓ, U ℓ ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ x, sigStateMW L U x = ![trig L p x, trig L q x]

/-- `iX`. -/
def iXm : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

theorem iXm_mem_SU2 : iXm ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  -- PROVIDED SOLUTION
  -- `Matrix.mem_specialUnitaryGroup_iff`: unitary (`Matrix.mem_unitaryGroup_iff`, `star iXm * iXm = 1` entrywise with
  -- `Matrix.star_eq_conjTranspose`, `ext i j; fin_cases i <;> fin_cases j <;> simp [iXm, Matrix.mul_apply]`) and
  -- `det iXm = 0·0 − I·I = 1` (`Matrix.det_fin_two`, `Complex.I_mul_I`).
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [iXm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [iXm, Matrix.det_fin_two]

/-- `diag(e^{ix}, 1) = −(iX) diag(1, e^{ix}) (iX)`. -/
theorem sigMatMW_eq (x : ℝ) : sigMatMW x = -(iXm * sigMat x * iXm) := by
  -- PROVIDED SOLUTION
  -- `ext i j; fin_cases i <;> fin_cases j <;> simp [sigMatMW, sigMat, iXm, Matrix.mul_apply, Fin.sum_univ_two]`;
  -- the remaining goals are `I * e * I = −e` and `I * I = −1` (`Complex.I_mul_I`, `ring`).
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigMatMW, sigMat, iXm]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- Every element of U(2) is a phase times an element of SU(2). -/
theorem unitary2_eq_phase_smul_SU2 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ U = c • V := by
  -- PROVIDED SOLUTION
  -- `‖det U‖ = 1` (`Matrix.det_of_mem_unitary`, or `star (det U) * det U = 1` from `det (star U * U) = 1`). Take `c` with
  -- `c ^ 2 = det U` (`IsAlgClosed.exists_pow_nat_eq (det U) (by norm_num : 0 < 2)`); then `‖c‖ ^ 2 = 1`, so `‖c‖ = 1` and
  -- `c ≠ 0`. Let `V = c⁻¹ • U`. `V` is unitary (`star V * V = (‖c‖⁻²) • (star U * U) = 1`, using `star c * c = 1`), and
  -- `det V = c⁻¹ ^ 2 * det U = 1` (`Matrix.det_smul`, `Fintype.card_fin`). `U = c • V` by `smul_smul`, `mul_inv_cancel₀`.
  have hdet : ‖U.det‖ = 1 := by
    have h1 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hU)
    have h2 : (Complex.normSq U.det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h1
    have h3 : Complex.normSq U.det = 1 := by exact_mod_cast h2
    have h4 : ‖U.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h3]
    have h0 : 0 ≤ ‖U.det‖ := norm_nonneg _
    nlinarith
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq U.det (by norm_num : 0 < 2)
  have hcn : ‖c‖ = 1 := by
    have h2 : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc, hdet]
    have h0 : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcn; exact zero_ne_one hcn
  have hsc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hcn]; simp
  refine ⟨c, hcn, c⁻¹ • U, ?_, ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU
      rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul]
      have : c⁻¹ * star c⁻¹ = 1 := by
        rw [star_inv₀, ← mul_inv, mul_comm, hsc, inv_one]
      rw [this, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, ← hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hc0)]
  · rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]

/-- Left-multiplying the last element of the sequence multiplies the state. -/
theorem sigState_mul_last (L : ℕ) (V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    sigState L (Function.update V (Fin.last L) (A * V (Fin.last L))) x = A *ᵥ sigState L V x := by
  -- PROVIDED SOLUTION
  -- `cases L` and unfold one step of `sigState`. In both cases the last index is `Fin.last L`, the inner sequence
  -- `fun i => _ (Fin.castSucc i)` is unchanged (`Function.update_of_ne`, `Fin.castSucc_lt_last`, `ne_of_lt`), and
  -- `(A * B) *ᵥ v = A *ᵥ (B *ᵥ v)` (`Matrix.mulVec_mulVec`).
  cases L with
  | zero =>
    simp only [sigState]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Function.update_self, Matrix.mulVec_mulVec]
  | succ L =>
    have hf : (fun i : Fin (L + 1) => Function.update V (Fin.last (L + 1)) (A * V (Fin.last (L + 1)))
        (Fin.castSucc i)) = fun i => V (Fin.castSucc i) := by
      funext i
      rw [Function.update_of_ne (ne_of_lt (Fin.castSucc_lt_last i))]
    simp only [sigState, hf, Function.update_self, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The key step: `iX` times a sequence in the convention of Motlagh and Wiebe is a phase times a sequence of SU(2) elements
    with the signal `diag(1, e^{ix})`. -/
theorem iXm_mul_sigStateMW (L : ℕ) (U : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ ℓ, U ℓ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ V : Fin (L + 1) → Matrix (Fin 2) (Fin 2) ℂ, (∀ ℓ, V ℓ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ x, iXm *ᵥ sigStateMW L U x = φ • sigState L V x := by
  -- PROVIDED SOLUTION
  -- Induction on `L` (generalising `U`).
  -- L = 0: write `U 0 = c • W` with `W ∈ SU(2)`, `‖c‖ = 1` (`unitary2_eq_phase_smul_SU2`). Take `V 0 = iXm * W` (in SU(2):
  -- `mul_mem iXm_mem_SU2 hW`) and `φ = c`: `iXm *ᵥ (U 0 *ᵥ e₀) = c • ((iXm * W) *ᵥ e₀)` (`Matrix.mulVec_mulVec`,
  -- `Matrix.mulVec_smul`, `Matrix.smul_mulVec_assoc`).
  -- L + 1: by `sigStateMW`, `iXm *ᵥ sigStateMW (L+1) U x = iXm *ᵥ (U last *ᵥ (sigMatMW x *ᵥ s))` with
  -- `s = sigStateMW L (U ∘ castSucc) x`. Write `U last = c • W` and use `sigMatMW_eq`:
  -- `iXm * U last * sigMatMW x = −c • (iXm * W * iXm) * sigMat x * iXm`. The induction hypothesis for `U ∘ castSucc` gives
  -- `V'`, `φ'` with `iXm *ᵥ s = φ' • sigState L V' x`. Take `V = Fin.lastCases (iXm * W * iXm) V'` (so that `V last =
  -- iXm * W * iXm ∈ SU(2)` and `V ∘ castSucc = V'`; `Fin.lastCases_last`, `Fin.lastCases_castSucc`) and `φ = −c * φ'`
  -- (`‖φ‖ = 1` by `norm_mul`, `norm_neg`). Then `sigState (L+1) V x = V last *ᵥ (sigMat x *ᵥ sigState L V' x)` closes the
  -- goal after `Matrix.mulVec_mulVec`, `Matrix.mulVec_smul`, `Matrix.neg_mulVec`, `smul_smul`.
  induction L with
  | zero =>
    obtain ⟨c, hc, W, hW, hUW⟩ := unitary2_eq_phase_smul_SU2 (U 0) (hU 0)
    refine ⟨fun _ => iXm * W, fun _ => mul_mem iXm_mem_SU2 hW, c, hc, fun x => ?_⟩
    simp only [sigStateMW, sigState, hUW]
    rw [Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mulVec]
  | succ L ih =>
    obtain ⟨c, hc, W, hW, hUW⟩ := unitary2_eq_phase_smul_SU2 _ (hU (Fin.last (L + 1)))
    obtain ⟨V', hV', φ', hφ', hV'x⟩ := ih (fun i => U (Fin.castSucc i)) (fun i => hU _)
    refine ⟨Fin.lastCases (iXm * W * iXm) V', ?_, -c * φ', ?_, fun x => ?_⟩
    · intro ℓ
      refine Fin.lastCases ?_ (fun i => ?_) ℓ
      · dsimp only; rw [Fin.lastCases_last]
        exact mul_mem (mul_mem iXm_mem_SU2 hW) iXm_mem_SU2
      · dsimp only; rw [Fin.lastCases_castSucc]; exact hV' i
    · rw [norm_mul, norm_neg, hc, hφ', one_mul]
    · have hV'' : (fun i : Fin (L + 1) => (Fin.lastCases (iXm * W * iXm) V' : Fin (L + 2) → _)
          (Fin.castSucc i)) = V' := by
        funext i; exact Fin.lastCases_castSucc i
      simp only [sigStateMW, sigState, hV'', Fin.lastCases_last]
      have key : iXm * (c • W) * sigMatMW x = (-c) • (iXm * W * iXm * sigMat x) * iXm := by
        rw [sigMatMW_eq]
        have : iXm * (c • W) * -(iXm * sigMat x * iXm) = (-c) • (iXm * W * iXm * sigMat x * iXm) := by
          rw [Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
          simp only [Matrix.mul_assoc]
        rw [this, Matrix.smul_mul]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUW, key, ← Matrix.mulVec_mulVec, hV'x x,
        Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, smul_smul, mul_comm φ']

/-- **Generalised QSP, conversion of conventions (proof of Lemma 3.3(i)).** Theorem 3 of Motlagh and Wiebe in their
    convention (`GQSPHypMW`) implies the form `GQSPHyp` used in this file. -/
theorem gqspHyp_of_MW (h : GQSPHypMW) : GQSPHyp := by
  -- PROVIDED SOLUTION
  -- `intro L p q hp hq hn`; `obtain ⟨U, hU, hUpq⟩ := h L p q hp hq hn`; `obtain ⟨V, hV, φ, hφ, hVx⟩ :=
  -- iXm_mul_sigStateMW L U hU`. Then `iXm *ᵥ ![p, q] = φ • sigState L V x`. Since `(-iXm) * iXm = 1`
  -- (`ext; fin_cases ...; simp [iXm, Complex.I_mul_I]`), `![p, q] = φ • ((-iXm) *ᵥ sigState L V x)`. Let
  -- `V' = Function.update V (Fin.last L) ((-iXm) * V (Fin.last L))`: in SU(2) (`-iXm ∈ SU(2)`: `det (-iXm) = det iXm = 1`
  -- by `Matrix.det_neg`, `Fintype.card_fin`, and unitary), and `sigState L V' x = (-iXm) *ᵥ sigState L V x`
  -- (`sigState_mul_last`). So `sigState L V' x = φ⁻¹ • ![p, q]` with `‖φ⁻¹‖ = 1` (`norm_inv`, `φ ≠ 0`); use `⟨V', hV', φ⁻¹, _, _⟩`.
  intro L p q hp hq hn
  obtain ⟨U, hU, hUpq⟩ := h L p q hp hq hn
  obtain ⟨V, hV, φ, hφ, hVx⟩ := iXm_mul_sigStateMW L U hU
  have hii : (-iXm) * iXm = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iXm, Matrix.mul_apply, Fin.sum_univ_two]
  have hnegSU : -iXm ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    have h1 := iXm_mem_SU2
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [star_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h1.1]
    · rw [Matrix.det_neg, Fintype.card_fin, h1.2]; norm_num
  have hφ0 : φ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hφ; exact zero_ne_one hφ
  refine ⟨Function.update V (Fin.last L) ((-iXm) * V (Fin.last L)), ?_, φ⁻¹, ?_, fun x => ?_⟩
  · intro ℓ
    by_cases hl : ℓ = Fin.last L
    · subst hl; rw [Function.update_self]; exact mul_mem hnegSU (hV _)
    · rw [Function.update_of_ne hl]; exact hV ℓ
  · rw [norm_inv, hφ, inv_one]
  · rw [sigState_mul_last, ← hUpq x]
    have := congrArg (fun v => φ⁻¹ • ((-iXm) *ᵥ v)) (hVx x)
    simp only [Matrix.mulVec_mulVec, hii, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul,
      inv_mul_cancel₀ hφ0, one_smul] at this
    rw [this]

end

end
