import Mathlib

/-!
# Growth of the multiplier products

For `0 < p < 1/2` and `γ > 0` put `a_s = (1 - p) / (s + 1)^p`, `b_s = (1 - p) γ / (s + 1)`,
`m_s(ζ) = 1 - b_s + i ζ a_s` and `Φ_t(ζ) = ∏_{s < t} m_s(ζ)`.

On the region `R = {ζ | 1/2 ≤ Re ζ, Im ζ ≤ 0}` we bound `‖Φ_{t+1}(ζ)‖` below by `‖m_0(ζ)‖ G_t`,
where `G_t` does not depend on `ζ` and grows like `t^{1-2p}`. Hence `Σ_s b_s / G_s` converges.
-/

namespace LastIterate

open Complex Finset Filter Topology

/-- The gradient coefficient `a_s = (1 - p) / (s + 1)^p`. -/
noncomputable def coefA (p : ℝ) (s : ℕ) : ℝ := (1 - p) / ((s : ℝ) + 1) ^ p

/-- The anchor coefficient `b_s = (1 - p) γ / (s + 1)`. -/
noncomputable def coefB (p γ : ℝ) (s : ℕ) : ℝ := (1 - p) * γ / ((s : ℝ) + 1)

/-- The one-step multiplier `m_s(ζ) = 1 - b_s + i ζ a_s`. -/
noncomputable def mult (p γ : ℝ) (s : ℕ) (ζ : ℂ) : ℂ :=
  ((1 - coefB p γ s : ℝ) : ℂ) + I * ζ * (coefA p s : ℂ)

/-- The product `Φ_t(ζ) = ∏_{s < t} m_s(ζ)`. -/
noncomputable def prodMult (p γ : ℝ) (t : ℕ) (ζ : ℂ) : ℂ := ∏ s ∈ range t, mult p γ s ζ

/-- The closed region `R = {ζ | 1/2 ≤ Re ζ, Im ζ ≤ 0}`. -/
def regionR : Set ℂ := {ζ | 1 / 2 ≤ ζ.re ∧ ζ.im ≤ 0}

/-- A lower bound for `‖m_s(ζ)‖` on `R`, see `norm_mult_ge_lowFac`. -/
noncomputable def lowFac (p : ℝ) (S0 s : ℕ) : ℝ :=
  if s < S0 then coefA p s / 2 else 1 + coefA p s ^ 2 / 32

/-- The `ζ`-independent lower bound `G_t = ∏_{j < t} ℓ_{j+1}`. -/
noncomputable def lowProd (p : ℝ) (S0 t : ℕ) : ℝ := ∏ j ∈ range t, lowFac p S0 (j + 1)

variable {p γ : ℝ}

lemma rpow_one_sub_two_mul {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x ^ (1 - 2 * p) = x / (x ^ p) ^ 2 := by
  rw [Real.rpow_sub hx, Real.rpow_one, ← Real.rpow_natCast (x ^ p) 2, ← Real.rpow_mul hx.le,
    show p * ((2 : ℕ) : ℝ) = 2 * p by push_cast; ring]

lemma rpow_two_sub_two_mul {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x ^ (2 - 2 * p) = x * (x / (x ^ p) ^ 2) := by
  rw [show (2 : ℝ) - 2 * p = 1 + (1 - 2 * p) by ring, Real.rpow_add hx, Real.rpow_one,
    rpow_one_sub_two_mul hx]

lemma coefA_pos (hp1 : p < 1) (s : ℕ) : 0 < coefA p s :=
  div_pos (by linarith) (Real.rpow_pos_of_pos (by positivity) p)

lemma coefA_le_one (hp0 : 0 ≤ p) (s : ℕ) : coefA p s ≤ 1 := by
  have h1 : 1 ≤ ((s : ℝ) + 1) ^ p :=
    Real.one_le_rpow (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]) hp0
  rw [coefA, div_le_one (by linarith)]
  linarith

lemma coefB_pos (hp1 : p < 1) (hγ : 0 < γ) (s : ℕ) : 0 < coefB p γ s :=
  div_pos (mul_pos (by linarith) hγ) (by positivity)

lemma mult_re (s : ℕ) (ζ : ℂ) :
    (mult p γ s ζ).re = 1 - coefB p γ s - coefA p s * ζ.im := by
  simp only [mult, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  ring

lemma mult_im (s : ℕ) (ζ : ℂ) : (mult p γ s ζ).im = coefA p s * ζ.re := by
  simp only [mult, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_re]
  ring

lemma norm_mult_ge_half (hp1 : p < 1) {ζ : ℂ} (hζ : ζ ∈ regionR) (s : ℕ) :
    coefA p s / 2 ≤ ‖mult p γ s ζ‖ := by
  have ha := coefA_pos hp1 s
  have h1 := abs_im_le_norm (mult p γ s ζ)
  rw [mult_im] at h1
  have hre : 1 / 2 ≤ ζ.re := hζ.1
  have h2 : coefA p s / 2 ≤ coefA p s * ζ.re := by nlinarith
  linarith [le_abs_self (coefA p s * ζ.re)]

lemma norm_mult_ge_one (hp0 : 0 ≤ p) (hp1 : p < 1) {ζ : ℂ} (hζ : ζ ∈ regionR) {s : ℕ}
    (hs : 16 * coefB p γ s ≤ coefA p s ^ 2) :
    1 + coefA p s ^ 2 / 32 ≤ ‖mult p γ s ζ‖ := by
  have ha := coefA_pos hp1 s
  have ha1 := coefA_le_one hp0 s
  have hre := mult_re (p := p) (γ := γ) s ζ
  have him := mult_im (p := p) (γ := γ) s ζ
  have hζre : 1 / 2 ≤ ζ.re := hζ.1
  have hζim : ζ.im ≤ 0 := hζ.2
  set a := coefA p s
  set b := coefB p γ s
  set m := mult p γ s ζ
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hb : b ≤ 1 / 16 := by nlinarith
  have hre_ge : 1 - b ≤ m.re := by rw [hre]; nlinarith
  have him_ge : a / 2 ≤ m.im := by rw [him]; nlinarith
  have hsq : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have h1 : (1 - b) ^ 2 ≤ m.re ^ 2 := pow_le_pow_left₀ (by linarith) hre_ge 2
  have h2 : (a / 2) ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ (by linarith) him_ge 2
  have hn2 : 1 + a ^ 2 / 8 ≤ ‖m‖ ^ 2 := by nlinarith
  have hn0 : 0 ≤ ‖m‖ := norm_nonneg _
  by_contra hlt
  push Not at hlt
  have h3 : ‖m‖ ^ 2 < (1 + a ^ 2 / 32) ^ 2 := pow_lt_pow_left₀ hlt hn0 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg a)]

/-- Beyond some threshold `S0`, `16 b_s ≤ a_s^2`. -/
lemma exists_threshold (hp0 : 0 < p) (hp2 : p < 1 / 2) :
    ∃ S0 : ℕ, ∀ s ≥ S0, 16 * coefB p γ s ≤ coefA p s ^ 2 := by
  have h1p : 0 < 1 - p := by linarith
  have hpos : 0 < 1 - 2 * p := by linarith
  have ht : Tendsto (fun s : ℕ => ((s : ℝ) + 1) ^ (1 - 2 * p)) atTop atTop :=
    (tendsto_rpow_atTop hpos).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (16 * γ / (1 - p)))
  refine ⟨S0, fun s hs => ?_⟩
  have h := hS0 s hs
  have hx : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hq : 0 < ((s : ℝ) + 1) ^ p := Real.rpow_pos_of_pos hx p
  rw [rpow_one_sub_two_mul hx, div_le_div_iff₀ h1p (by positivity)] at h
  rw [coefA, coefB, div_pow, mul_div_assoc', div_le_div_iff₀ hx (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h h1p.le]

lemma lowFac_pos (hp1 : p < 1) (S0 s : ℕ) : 0 < lowFac p S0 s := by
  have := coefA_pos hp1 s
  unfold lowFac
  split_ifs <;> positivity

lemma lowProd_pos (hp1 : p < 1) (S0 t : ℕ) : 0 < lowProd p S0 t :=
  prod_pos fun j _ => lowFac_pos hp1 S0 (j + 1)

lemma norm_mult_ge_lowFac (hp0 : 0 ≤ p) (hp1 : p < 1) {S0 : ℕ}
    (hS0 : ∀ s ≥ S0, 16 * coefB p γ s ≤ coefA p s ^ 2) {ζ : ℂ} (hζ : ζ ∈ regionR) (s : ℕ) :
    lowFac p S0 s ≤ ‖mult p γ s ζ‖ := by
  unfold lowFac
  split_ifs with h
  · exact norm_mult_ge_half hp1 hζ s
  · exact norm_mult_ge_one hp0 hp1 hζ (hS0 s (not_lt.mp h))

/-- The uniform lower bound `‖m_0(ζ)‖ G_t ≤ ‖Φ_{t+1}(ζ)‖` on `R`. -/
lemma norm_prodMult_ge (hp0 : 0 ≤ p) (hp1 : p < 1) {S0 : ℕ}
    (hS0 : ∀ s ≥ S0, 16 * coefB p γ s ≤ coefA p s ^ 2) {ζ : ℂ} (hζ : ζ ∈ regionR) (t : ℕ) :
    ‖mult p γ 0 ζ‖ * lowProd p S0 t ≤ ‖prodMult p γ (t + 1) ζ‖ := by
  rw [prodMult, prod_range_succ', norm_mul, norm_prod, mul_comm (‖mult p γ 0 ζ‖)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact prod_le_prod (fun j _ => (lowFac_pos hp1 S0 (j + 1)).le)
    (fun j _ => norm_mult_ge_lowFac hp0 hp1 hS0 hζ (j + 1))

lemma one_add_sum_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hxi : 0 ≤ x i := hx i (mem_insert_self i s)
    have hs : ∀ j ∈ s, 0 ≤ x j := fun j hj => hx j (mem_insert_of_mem hj)
    have ih' := ih hs
    have hsum : 0 ≤ ∑ j ∈ s, x j := sum_nonneg hs
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 + x i),
      mul_nonneg hxi hsum]

/-- `G_t` grows at least like `(t + 1)^{1 - 2p}`, written as `(t + 1) / ((t + 1)^p)^2`. -/
lemma lowProd_ge (hp0 : 0 < p) (hp1 : p < 1) (S0 : ℕ) :
    ∃ κ > 0, ∀ t ≥ 2 * S0 + 1,
      κ * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2) ≤ lowProd p S0 t := by
  have h1p : 0 < 1 - p := by linarith
  set P0 := ∏ j ∈ range S0, lowFac p S0 (j + 1) with hP0
  have hP0pos : 0 < P0 := prod_pos fun j _ => lowFac_pos hp1 S0 (j + 1)
  refine ⟨P0 * (1 - p) ^ 2 / 64, div_pos (mul_pos hP0pos (pow_pos h1p 2)) (by norm_num),
    fun t ht => ?_⟩
  have hS0t : S0 ≤ t := by omega
  have hsplit : lowProd p S0 t = P0 * ∏ j ∈ Ico S0 t, (1 + coefA p (j + 1) ^ 2 / 32) := by
    rw [lowProd, ← prod_range_mul_prod_Ico _ hS0t]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have hj' : ¬ (j + 1 < S0) := by
      rw [mem_Ico] at hj
      omega
    simp only [lowFac, if_neg hj']
  have hx : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hq : 0 < ((t : ℝ) + 1) ^ p := Real.rpow_pos_of_pos hx p
  have hterm : ∀ j ∈ Ico S0 t,
      ((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32 ≤ coefA p (j + 1) ^ 2 / 32 := by
    intro j hj
    rw [mem_Ico] at hj
    have hj' : ((j + 1 : ℕ) : ℝ) + 1 ≤ (t : ℝ) + 1 := by
      have hjt : j + 1 ≤ t := hj.2
      have : ((j + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hjt
      linarith
    have hpos : 0 < (((j + 1 : ℕ) : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
    have hle : (((j + 1 : ℕ) : ℝ) + 1) ^ p ≤ ((t : ℝ) + 1) ^ p :=
      Real.rpow_le_rpow (by positivity) hj' hp0.le
    have h1 : (1 - p) / ((t : ℝ) + 1) ^ p ≤ coefA p (j + 1) :=
      div_le_div_of_nonneg_left h1p.le hpos hle
    have h2 : 0 ≤ (1 - p) / ((t : ℝ) + 1) ^ p := div_nonneg h1p.le hq.le
    have h3 := pow_le_pow_left₀ h2 h1 2
    linarith
  have hsum : ((t : ℝ) - S0) * (((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32) ≤
      ∑ j ∈ Ico S0 t, coefA p (j + 1) ^ 2 / 32 := by
    have h := card_nsmul_le_sum (Ico S0 t) (fun j => coefA p (j + 1) ^ 2 / 32) _ hterm
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hS0t] at h
    exact h
  have hprod := one_add_sum_le_prod (Ico S0 t) (fun j => coefA p (j + 1) ^ 2 / 32)
    (fun j _ => by positivity)
  have htS : ((t : ℝ) + 1) / 2 ≤ (t : ℝ) - S0 := by
    have : ((2 * S0 + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    push_cast at this
    linarith
  have hc : 0 ≤ ((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32 := by positivity
  have hmain : (1 - p) ^ 2 / 64 * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2) ≤
      ∏ j ∈ Ico S0 t, (1 + coefA p (j + 1) ^ 2 / 32) := by
    have e : (1 - p) ^ 2 / 64 * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2) =
        ((t : ℝ) + 1) / 2 * (((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32) := by
      ring
    rw [e]
    calc ((t : ℝ) + 1) / 2 * (((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32)
        ≤ ((t : ℝ) - S0) * (((1 - p) / ((t : ℝ) + 1) ^ p) ^ 2 / 32) :=
          mul_le_mul_of_nonneg_right htS hc
      _ ≤ ∑ j ∈ Ico S0 t, coefA p (j + 1) ^ 2 / 32 := hsum
      _ ≤ 1 + ∑ j ∈ Ico S0 t, coefA p (j + 1) ^ 2 / 32 := by linarith
      _ ≤ ∏ j ∈ Ico S0 t, (1 + coefA p (j + 1) ^ 2 / 32) := hprod
  rw [hsplit]
  calc P0 * (1 - p) ^ 2 / 64 * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2)
      = P0 * ((1 - p) ^ 2 / 64 * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2)) := by ring
    _ ≤ P0 * ∏ j ∈ Ico S0 t, (1 + coefA p (j + 1) ^ 2 / 32) :=
      mul_le_mul_of_nonneg_left hmain hP0pos.le

/-- `G_t` is eventually bounded below by a positive constant. -/
lemma exists_lowProd_ge_const (hp0 : 0 < p) (hp2 : p < 1 / 2) (S0 : ℕ) :
    ∃ δ > 0, ∃ T₀ : ℕ, ∀ t ≥ T₀, δ ≤ lowProd p S0 t := by
  obtain ⟨κ, hκ, hG⟩ := lowProd_ge hp0 (by linarith) S0
  refine ⟨κ, hκ, 2 * S0 + 1, fun t ht => ?_⟩
  have hx : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have h1 : 1 ≤ ((t : ℝ) + 1) ^ (1 - 2 * p) :=
    Real.one_le_rpow (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]) (by linarith)
  rw [rpow_one_sub_two_mul hx] at h1
  calc κ = κ * 1 := (mul_one κ).symm
    _ ≤ κ * (((t : ℝ) + 1) / (((t : ℝ) + 1) ^ p) ^ 2) := mul_le_mul_of_nonneg_left h1 hκ.le
    _ ≤ lowProd p S0 t := hG t ht

/-- The series `Σ_s b_s / G_s` converges. -/
lemma summable_coefB_div_lowProd (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) (S0 : ℕ) :
    Summable (fun s => coefB p γ s / lowProd p S0 s) := by
  have hp1 : p < 1 := by linarith
  obtain ⟨κ, hκ, hG⟩ := lowProd_ge hp0 hp1 S0
  have hsum : Summable (fun s : ℕ => (1 - p) * γ / κ * (1 / ((s : ℝ) + 1) ^ (2 - 2 * p))) := by
    apply Summable.mul_left
    have h := Real.summable_one_div_nat_rpow.mpr (by linarith : (1 : ℝ) < 2 - 2 * p)
    have h' := (summable_nat_add_iff 1).mpr h
    simpa using h'
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [eventually_ge_atTop (2 * S0 + 1)] with s hs
  have hGs := hG s hs
  have hx : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hq : 0 < ((s : ℝ) + 1) ^ p := Real.rpow_pos_of_pos hx p
  have hG0 : 0 < κ * (((s : ℝ) + 1) / (((s : ℝ) + 1) ^ p) ^ 2) := by positivity
  have hpos := lowProd_pos hp1 S0 s
  have hb := coefB_pos hp1 hγ s
  rw [Real.norm_of_nonneg (div_pos hb hpos).le, rpow_two_sub_two_mul hx]
  calc coefB p γ s / lowProd p S0 s
      ≤ coefB p γ s / (κ * (((s : ℝ) + 1) / (((s : ℝ) + 1) ^ p) ^ 2)) :=
        div_le_div_of_nonneg_left hb.le hG0 hGs
    _ = (1 - p) * γ / κ * (1 / (((s : ℝ) + 1) * (((s : ℝ) + 1) / (((s : ℝ) + 1) ^ p) ^ 2))) := by
        rw [coefB]
        generalize (s : ℝ) + 1 = X
        ring

end LastIterate
