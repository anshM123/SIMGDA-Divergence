import DMSolutions.LastIterate.Defs
import DMSolutions.LastIterate.Analytic

/-!
# The bilinear game and its iterates

For `ρ ∈ [1/2, 1]` let `L(x, y) = ρ x y` on `Z_space 1 1`. Its operator
`F(x, y) = (ρ y, -ρ x)` is monotone and `1`-Lipschitz, and `0` is a saddle point with `F 0 = 0`.

Started at `z_init = (1, 0)`, the iteration `step` with `coefficients_schedule_p p γ 1` acts on
`w = x + i y` as `w_{t+1} = m_t(ρ) w_t + b_t`, so `w_t = Φ_t(ρ) (1 + Σ_{s<t} b_s / Φ_{s+1}(ρ))`.
If `Λ(ρ) ≠ 0`, then `‖F z_t‖ = ρ |w_t|` stays away from `0`, so `‖F z_T‖² ≤ C / T` fails.
-/

namespace LastIterate

open Arxiv.«1905.10899» Complex Finset Filter Topology

/-- The first coordinate `x` of `z = (x, y) ∈ Z_space 1 1`. -/
noncomputable def coordX : Z_space 1 1 →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.fst ℝ (E_n 1) (F_m 1)).comp (toProd 1 1).toContinuousLinearMap)

/-- The second coordinate `y` of `z = (x, y) ∈ Z_space 1 1`. -/
noncomputable def coordY : Z_space 1 1 →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ (E_n 1) (F_m 1)).comp (toProd 1 1).toContinuousLinearMap)

lemma coordX_apply (z : Z_space 1 1) : coordX z = (toProd 1 1 z).1 0 := rfl

lemma coordY_apply (z : Z_space 1 1) : coordY z = (toProd 1 1 z).2 0 := rfl

lemma coordX_symm (a : E_n 1) (b : F_m 1) : coordX ((toProd 1 1).symm (a, b)) = a 0 := by
  simp [coordX_apply]

lemma coordY_symm (a : E_n 1) (b : F_m 1) : coordY ((toProd 1 1).symm (a, b)) = b 0 := by
  simp [coordY_apply]

lemma inner_eq_coord (u v : Z_space 1 1) :
    inner ℝ u v = coordX u * coordX v + coordY u * coordY v := by
  simp [coordX_apply, coordY_apply, toProd, PiLp.inner_apply]
  ring

lemma norm_sq_eq_coord (u : Z_space 1 1) : ‖u‖ ^ 2 = coordX u ^ 2 + coordY u ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coord]
  ring

/-- The bilinear game `L(x, y) = ρ x y`. -/
noncomputable def gameL (ρ : ℝ) (z : Z_space 1 1) : ℝ := ρ * (coordX z * coordY z)

lemma hasGradientAt_gameL (ρ : ℝ) (z : Z_space 1 1) :
    HasGradientAt (gameL ρ)
      ((toProd 1 1).symm (ρ • (toProd 1 1 z).2, ρ • (toProd 1 1 z).1)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun y => ρ * (coordX y * coordY y))
      (ρ • (coordX z • coordY + coordY z • coordX)) z :=
    ((coordX.hasFDerivAt (x := z)).mul (coordY.hasFDerivAt (x := z))).const_mul ρ
  refine h.congr_fderiv ?_
  ext v
  rw [InnerProductSpace.toDual_apply_apply, inner_eq_coord, coordX_symm, coordY_symm]
  simp [coordX_apply, coordY_apply]
  ring

lemma differentiable_gameL (ρ : ℝ) : Differentiable ℝ (gameL ρ) :=
  fun z => (hasGradientAt_gameL ρ z).differentiableAt

lemma F_operator_gameL (ρ : ℝ) (z : Z_space 1 1) :
    F_operator 1 1 (gameL ρ) z =
      (toProd 1 1).symm (ρ • (toProd 1 1 z).2, -(ρ • (toProd 1 1 z).1)) := by
  simp only [F_operator, (hasGradientAt_gameL ρ z).gradient,
    ContinuousLinearEquiv.apply_symm_apply]

lemma coordX_F (ρ : ℝ) (z : Z_space 1 1) :
    coordX (F_operator 1 1 (gameL ρ) z) = ρ * coordY z := by
  rw [F_operator_gameL, coordX_symm]
  simp [coordY_apply]

lemma coordY_F (ρ : ℝ) (z : Z_space 1 1) :
    coordY (F_operator 1 1 (gameL ρ) z) = -(ρ * coordX z) := by
  rw [F_operator_gameL, coordY_symm]
  simp [coordX_apply]

lemma monotone_gameL (ρ : ℝ) : ∀ z w : Z_space 1 1,
    inner ℝ (F_operator 1 1 (gameL ρ) z - F_operator 1 1 (gameL ρ) w) (z - w) ≥ (0 : ℝ) := by
  intro z w
  rw [inner_eq_coord]
  simp only [map_sub, coordX_F, coordY_F]
  rw [ge_iff_le]
  apply le_of_eq
  ring

lemma lipschitz_gameL {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : ∀ z w : Z_space 1 1,
    ‖F_operator 1 1 (gameL ρ) z - F_operator 1 1 (gameL ρ) w‖ ≤
      ((1 : NNReal) : ℝ) * ‖z - w‖ := by
  intro z w
  rw [NNReal.coe_one, one_mul]
  have h1 := norm_sq_eq_coord (F_operator 1 1 (gameL ρ) z - F_operator 1 1 (gameL ρ) w)
  have h2 := norm_sq_eq_coord (z - w)
  simp only [map_sub, coordX_F, coordY_F] at h1 h2
  have h3 : ‖F_operator 1 1 (gameL ρ) z - F_operator 1 1 (gameL ρ) w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [h1, h2]
    have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (coordX z - coordX w), sq_nonneg (coordY z - coordY w)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h3

lemma isSaddlePoint_gameL (ρ : ℝ) : IsSaddlePoint 1 1 (gameL ρ) 0 := by
  show (∀ y : F_m 1, gameL ρ ((toProd 1 1).symm (0, y)) ≤ gameL ρ 0) ∧
    ∀ x : E_n 1, gameL ρ 0 ≤ gameL ρ ((toProd 1 1).symm (x, 0))
  refine ⟨fun y => ?_, fun x => ?_⟩ <;> simp [gameL, coordX_symm, coordY_symm]

lemma F_gameL_zero (ρ : ℝ) : F_operator 1 1 (gameL ρ) 0 = 0 := by
  simp [F_operator_gameL]

/-- The initial point `z_init = (1, 0)`. -/
noncomputable def zInit : Z_space 1 1 := (toProd 1 1).symm (EuclideanSpace.single 0 1, 0)

lemma coordX_zInit : coordX zInit = 1 := by simp [zInit, coordX_symm]

lemma coordY_zInit : coordY zInit = 0 := by simp [zInit, coordY_symm]

/-- The run of `step` with `coefficients_schedule_p p γ 1`, anchored at `zInit`. -/
noncomputable def iter (ρ p γ : ℝ) : ℕ → State 1 1
  | 0 => { z := zInit, z0 := zInit, t := 0, history := [zInit] }
  | t + 1 => step 1 1 (gameL ρ) (iter ρ p γ t)
      (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).1
      (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).2

lemma iter_z0 (ρ p γ : ℝ) (t : ℕ) : (iter ρ p γ t).z0 = zInit := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

lemma iter_z_succ (ρ p γ : ℝ) (t : ℕ) :
    (iter ρ p γ (t + 1)).z = (iter ρ p γ t).z
      - (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).1 •
          F_operator 1 1 (gameL ρ) (iter ρ p γ t).z
      + (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).2 • (zInit - (iter ρ p γ t).z) := by
  rw [← iter_z0 ρ p γ t]
  rfl

lemma coef_fst (p γ : ℝ) (t : ℕ) :
    (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).1 = coefA p t := by
  simp only [coefficients_schedule_p, coefA, NNReal.coe_one, one_mul, Real.rpow_eq_pow]

lemma coef_snd (p γ : ℝ) (t : ℕ) :
    (coefficients_schedule_p p γ ((1 : NNReal) : ℝ) t).2 = coefB p γ t := by
  simp only [coefficients_schedule_p, coefB]

/-- The complex coordinate `w = x + i y`. -/
noncomputable def cplx (z : Z_space 1 1) : ℂ := (coordX z : ℂ) + (coordY z : ℂ) * I

lemma cplx_iter_succ (ρ p γ : ℝ) (t : ℕ) :
    cplx (iter ρ p γ (t + 1)).z = mult p γ t ρ * cplx (iter ρ p γ t).z + coefB p γ t := by
  rw [iter_z_succ, coef_fst, coef_snd]
  apply Complex.ext
  · simp [cplx, mult, coordX_F, coordY_F, coordX_zInit, coordY_zInit]
    ring
  · simp [cplx, mult, coordX_F, coordY_F, coordX_zInit, coordY_zInit]
    ring

lemma prodMult_succ (p γ : ℝ) (t : ℕ) (ζ : ℂ) :
    prodMult p γ (t + 1) ζ = prodMult p γ t ζ * mult p γ t ζ := by
  simp only [prodMult, prod_range_succ]

lemma cplx_iter_eq {p γ : ℝ} (hp1 : p < 1) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (t : ℕ) :
    cplx (iter ρ p γ t).z = prodMult p γ t ρ * (1 + ∑ s ∈ range t, term p γ s ρ) := by
  have hR : (ρ : ℂ) ∈ regionR := mem_regionR.mpr ⟨by rw [ofReal_re]; exact hρ, by rw [ofReal_im]⟩
  induction t with
  | zero =>
    show cplx zInit = _
    simp [prodMult, cplx, coordX_zInit, coordY_zInit]
  | succ t ih =>
    have hne : prodMult p γ (t + 1) (ρ : ℂ) ≠ 0 := prodMult_ne_zero hp1 hR (t + 1)
    have hterm : term p γ t ρ * prodMult p γ (t + 1) ρ = coefB p γ t := by
      rw [term]
      exact div_mul_cancel₀ _ hne
    rw [cplx_iter_succ, ih, sum_range_succ]
    rw [prodMult_succ] at hterm ⊢
    linear_combination (-1 : ℂ) * hterm

lemma norm_F_sq (ρ : ℝ) (z : Z_space 1 1) :
    ‖F_operator 1 1 (gameL ρ) z‖ ^ 2 = ρ ^ 2 * ‖cplx z‖ ^ 2 := by
  rw [norm_sq_eq_coord, coordX_F, coordY_F, Complex.sq_norm, normSq_apply]
  simp only [cplx, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im]
  ring

/-- **Divergence.** If `Λ(ρ) ≠ 0`, the iterates do not satisfy `‖F z_T‖² ≤ C / T`. -/
theorem not_rate {p γ : ℝ} (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) {ρ : ℝ}
    (hρ1 : 1 / 2 ≤ ρ) (hΛ : limFun p γ ρ ≠ 0) :
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
      ‖F_operator 1 1 (gameL ρ) (iter ρ p γ T).z‖ ^ 2 ≤ C / (T : ℝ)) := by
  rintro ⟨C, hC, hbound⟩
  have hp1 : p < 1 := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hR : (ρ : ℂ) ∈ regionR := mem_regionR.mpr ⟨by rw [ofReal_re]; exact hρ1, by rw [ofReal_im]⟩
  obtain ⟨S0, hS0⟩ := exists_threshold hp0 hp2
  obtain ⟨δ, hδ, T₀, hT₀⟩ := exists_lowProd_ge_const hp0 hp2 S0
  have hQ : Tendsto (fun t => 1 + ∑ s ∈ range t, term p γ s ρ) atTop (𝓝 (limFun p γ ρ)) := by
    have hs : Summable (fun s => term p γ s ρ) := (summable_norm_term hp0 hp2 hγ hR).of_norm
    exact (hs.hasSum.tendsto_sum_nat).const_add 1
  have hΛpos : 0 < ‖limFun p γ ρ‖ := norm_pos_iff.mpr hΛ
  have hQ' : ∀ᶠ t in atTop, ‖limFun p γ ρ‖ / 2 < ‖1 + ∑ s ∈ range (t + 1), term p γ s ρ‖ :=
    (hQ.comp (tendsto_add_atTop_nat 1)).norm.eventually_const_lt (half_lt_self hΛpos)
  have ha0 := coefA_pos hp1 0
  set η := coefA p 0 / 2 * δ * (‖limFun p γ ρ‖ / 2) with hηdef
  have hη : 0 < η := by positivity
  have hC' : ∀ᶠ t : ℕ in atTop, C / ((t + 1 : ℕ) : ℝ) < ρ ^ 2 * η ^ 2 := by
    have h : Tendsto (fun t : ℕ => C / ((t + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
    exact h.eventually_lt_const (by positivity)
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((hQ'.and hC').and (eventually_ge_atTop T₀)).exists
  have hb := hbound (t + 1) (by omega)
  rw [norm_F_sq, cplx_iter_eq hp1 hρ1] at hb
  have hΦ : coefA p 0 / 2 * δ ≤ ‖prodMult p γ (t + 1) ρ‖ := by
    have h1 := norm_prodMult_ge hp0.le hp1 hS0 hR t
    have h2 := norm_mult_ge_half (γ := γ) hp1 hR 0
    have h3 := hT₀ t ht3
    calc coefA p 0 / 2 * δ ≤ ‖mult p γ 0 ρ‖ * lowProd p S0 t :=
          mul_le_mul h2 h3 hδ.le (norm_nonneg _)
      _ ≤ _ := h1
  have hW : η ≤ ‖prodMult p γ (t + 1) ρ * (1 + ∑ s ∈ range (t + 1), term p γ s ρ)‖ := by
    rw [norm_mul]
    exact mul_le_mul hΦ ht1.le (by positivity) (norm_nonneg _)
  have hsq : ρ ^ 2 * η ^ 2 ≤
      ρ ^ 2 * ‖prodMult p γ (t + 1) ρ * (1 + ∑ s ∈ range (t + 1), term p γ s ρ)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hW 2) (sq_nonneg ρ)
  linarith

/-- The construction: all the data required by `divergence_for_p_lt_half`. -/
theorem divergence_main
  (p : ℝ) (hp1 : 0 < p) (hp2 : p < 1/2)
  (gamma : ℝ) (h_gamma : 2 ≤ gamma) :
  ∃ (n' m' : ℕ) (L : Z_space n' m' → ℝ)
    (K : NNReal) (_ : 0 < K)
    (_ : Differentiable ℝ L)
    (_ : ∀ z w : Z_space n' m',
      inner ℝ (F_operator n' m' L z - F_operator n' m' L w) (z - w) ≥ (0 : ℝ))
    (_ : ∀ z w : Z_space n' m',
      ‖F_operator n' m' L z - F_operator n' m' L w‖ ≤ K * ‖z - w‖)
    (z_star : Z_space n' m')
    (_ : IsSaddlePoint n' m' L z_star)
    (_ : F_operator n' m' L z_star = 0)
    (s_seq : ℕ → State n' m') (z_init : Z_space n' m')
    (_ : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
    (_ : ∀ t, s_seq (t + 1) = step n' m' L (s_seq t)
      (coefficients_schedule_p p gamma K t).1
      (coefficients_schedule_p p gamma K t).2),
  ¬ (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
    ‖F_operator n' m' L (s_seq T).z‖ ^ 2 ≤ C / (T : ℝ)) := by
  have hγ : 0 < gamma := by linarith
  obtain ⟨ρ, hρ1, hρ2, hΛ⟩ := exists_real_limFun_ne_zero hp1 hp2 hγ
  exact ⟨1, 1, gameL ρ, 1, one_pos, differentiable_gameL ρ, monotone_gameL ρ,
    lipschitz_gameL (by linarith) hρ2, 0, isSaddlePoint_gameL ρ, F_gameL_zero ρ,
    iter ρ p gamma, zInit, rfl, fun t => rfl, not_rate hp1 hp2 hγ hρ1 hΛ⟩

end LastIterate
