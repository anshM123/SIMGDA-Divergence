import DMSolutions.LastIterate.Uniqueness
import DMSolutions.LastIterate.Growth

/-!
# The limit function and a real parameter where it does not vanish

The function `Λ(ζ) = 1 + Σ_s b_s / Φ_{s+1}(ζ)` is continuous on `R`, holomorphic on the open
quadrant `V = {ζ | 1/2 < Re ζ, Im ζ < 0}`, and not zero at some point of `V`. If `Λ` vanished on
the whole real segment `[1/2, 1]`, then boundary uniqueness on the disk of centre `3/4` and
radius `1/4`, followed by the identity theorem on `V`, would make `Λ` zero on `V`.
-/

namespace LastIterate

open Complex Finset Filter Topology Metric Set

/-- The term `b_s / Φ_{s+1}(ζ)`. -/
noncomputable def term (p γ : ℝ) (s : ℕ) (ζ : ℂ) : ℂ :=
  (coefB p γ s : ℂ) / prodMult p γ (s + 1) ζ

/-- The limit function `Λ(ζ) = 1 + Σ_s b_s / Φ_{s+1}(ζ)`. -/
noncomputable def limFun (p γ : ℝ) (ζ : ℂ) : ℂ := 1 + ∑' s, term p γ s ζ

/-- The open region `V = {ζ | 1/2 < Re ζ, Im ζ < 0}`. -/
def regionV : Set ℂ := {ζ | 1 / 2 < ζ.re ∧ ζ.im < 0}

lemma mem_regionR {ζ : ℂ} : ζ ∈ regionR ↔ 1 / 2 ≤ ζ.re ∧ ζ.im ≤ 0 := Iff.rfl

lemma mem_regionV {ζ : ℂ} : ζ ∈ regionV ↔ 1 / 2 < ζ.re ∧ ζ.im < 0 := Iff.rfl

lemma isOpen_regionV : IsOpen regionV :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const)

lemma isPreconnected_regionV : IsPreconnected regionV :=
  ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_lt 0)).isPreconnected

lemma regionV_subset_regionR : regionV ⊆ regionR := fun _ h =>
  mem_regionR.mpr ⟨(mem_regionV.mp h).1.le, (mem_regionV.mp h).2.le⟩

variable {p γ : ℝ}

lemma differentiable_prodMult (t : ℕ) : Differentiable ℂ (fun ζ => prodMult p γ t ζ) := by
  simp only [prodMult, mult]
  fun_prop

lemma prodMult_ne_zero (hp1 : p < 1) {ζ : ℂ} (hζ : ζ ∈ regionR) (t : ℕ) :
    prodMult p γ t ζ ≠ 0 := by
  rw [prodMult, prod_ne_zero_iff]
  intro s _ h0
  have h := norm_mult_ge_half (γ := γ) hp1 hζ s
  have ha := coefA_pos hp1 s
  rw [h0, norm_zero] at h
  linarith

lemma norm_term_le (hp0 : 0 < p) (hp1 : p < 1) (hγ : 0 < γ) {S0 : ℕ}
    (hS0 : ∀ s ≥ S0, 16 * coefB p γ s ≤ coefA p s ^ 2) {ζ : ℂ} (hζ : ζ ∈ regionR) (s : ℕ) :
    ‖term p γ s ζ‖ ≤ coefB p γ s / lowProd p S0 s / ‖mult p γ 0 ζ‖ := by
  have hb := coefB_pos hp1 hγ s
  have hG := lowProd_pos hp1 S0 s
  have ha0 := coefA_pos hp1 0
  have hm0 : 0 < ‖mult p γ 0 ζ‖ := by
    have := norm_mult_ge_half (γ := γ) hp1 hζ 0
    linarith
  have hΦ := norm_prodMult_ge hp0.le hp1 hS0 hζ s
  rw [term, norm_div, norm_real, Real.norm_of_nonneg hb.le, div_div,
    mul_comm (lowProd p S0 s)]
  exact div_le_div_of_nonneg_left hb.le (mul_pos hm0 hG) hΦ

lemma norm_term_le_majorant (hp0 : 0 < p) (hp1 : p < 1) (hγ : 0 < γ) {S0 : ℕ}
    (hS0 : ∀ s ≥ S0, 16 * coefB p γ s ≤ coefA p s ^ 2) {ζ : ℂ} (hζ : ζ ∈ regionR) (s : ℕ) :
    ‖term p γ s ζ‖ ≤ coefB p γ s / lowProd p S0 s / (coefA p 0 / 2) := by
  refine (norm_term_le hp0 hp1 hγ hS0 hζ s).trans ?_
  have ha0 := coefA_pos hp1 0
  exact div_le_div_of_nonneg_left (div_pos (coefB_pos hp1 hγ s) (lowProd_pos hp1 S0 s)).le
    (by linarith) (norm_mult_ge_half hp1 hζ 0)

lemma summable_norm_term (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) {ζ : ℂ}
    (hζ : ζ ∈ regionR) : Summable (fun s => ‖term p γ s ζ‖) := by
  obtain ⟨S0, hS0⟩ := exists_threshold hp0 hp2
  exact Summable.of_nonneg_of_le (fun s => norm_nonneg _)
    (fun s => norm_term_le_majorant hp0 (by linarith) hγ hS0 hζ s)
    ((summable_coefB_div_lowProd hp0 hp2 hγ S0).div_const _)

lemma continuousOn_limFun (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) :
    ContinuousOn (limFun p γ) regionR := by
  have hp1 : p < 1 := by linarith
  obtain ⟨S0, hS0⟩ := exists_threshold hp0 hp2
  have hM := (summable_coefB_div_lowProd hp0 hp2 hγ S0).div_const (coefA p 0 / 2)
  have hterm : ∀ s, ContinuousOn (term p γ s) regionR := fun s =>
    continuousOn_const.div (differentiable_prodMult (s + 1)).continuous.continuousOn
      (fun ζ hζ => prodMult_ne_zero hp1 hζ (s + 1))
  have h := continuousOn_tsum hterm hM
    (fun s ζ hζ => norm_term_le_majorant hp0 hp1 hγ hS0 hζ s)
  exact continuousOn_const.add h

lemma differentiableOn_limFun (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) :
    DifferentiableOn ℂ (limFun p γ) regionV := by
  have hp1 : p < 1 := by linarith
  obtain ⟨S0, hS0⟩ := exists_threshold hp0 hp2
  have hM := (summable_coefB_div_lowProd hp0 hp2 hγ S0).div_const (coefA p 0 / 2)
  have hterm : ∀ s, DifferentiableOn ℂ (term p γ s) regionV := fun s =>
    (differentiableOn_const _).div (differentiable_prodMult (s + 1)).differentiableOn
      (fun ζ hζ => prodMult_ne_zero hp1 (regionV_subset_regionR hζ) (s + 1))
  have h := differentiableOn_tsum_of_summable_norm hM hterm isOpen_regionV
    (fun s ζ hζ => norm_term_le_majorant hp0 hp1 hγ hS0 (regionV_subset_regionR hζ) s)
  exact (differentiableOn_const 1).add h

/-- `Λ` does not vanish at some point of `V`, far below the real axis. -/
lemma exists_regionV_limFun_ne_zero (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) :
    ∃ ζ ∈ regionV, limFun p γ ζ ≠ 0 := by
  have hp1 : p < 1 := by linarith
  obtain ⟨S0, hS0⟩ := exists_threshold hp0 hp2
  have hsum := summable_coefB_div_lowProd hp0 hp2 hγ S0
  set S := ∑' s, coefB p γ s / lowProd p S0 s with hSdef
  have hS : 0 ≤ S :=
    tsum_nonneg fun s => (div_pos (coefB_pos hp1 hγ s) (lowProd_pos hp1 S0 s)).le
  have ha0 := coefA_pos hp1 0
  have hb0 := coefB_pos hp1 hγ 0
  set ε : ℝ := (S + coefB p γ 0) / coefA p 0 + 1 with hεdef
  have hε : 0 < ε := by positivity
  set ζ : ℂ := ⟨3 / 4, -ε⟩ with hζdef
  have hζV : ζ ∈ regionV := mem_regionV.mpr ⟨show (1 : ℝ) / 2 < 3 / 4 by norm_num,
    show -ε < 0 by linarith⟩
  have hζR := regionV_subset_regionR hζV
  have hm0 : S < ‖mult p γ 0 ζ‖ := by
    have h1 := re_le_norm (mult p γ 0 ζ)
    have hinv : coefA p 0 * (coefA p 0)⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    have h2 : (mult p γ 0 ζ).re = 1 + S + coefA p 0 := by
      rw [mult_re, show ζ.im = -ε from rfl, hεdef]
      linear_combination (S + coefB p γ 0) * hinv
    linarith
  refine ⟨ζ, hζV, fun h0 => ?_⟩
  have hm0pos : 0 < ‖mult p γ 0 ζ‖ := lt_of_le_of_lt hS hm0
  have hle : ∀ s, ‖term p γ s ζ‖ ≤ coefB p γ s / lowProd p S0 s / ‖mult p γ 0 ζ‖ :=
    fun s => norm_term_le hp0 hp1 hγ hS0 hζR s
  have hsumm : Summable (fun s => ‖term p γ s ζ‖) :=
    Summable.of_nonneg_of_le (fun s => norm_nonneg _) hle (hsum.div_const _)
  have hbound : ‖∑' s, term p γ s ζ‖ ≤ S / ‖mult p γ 0 ζ‖ := by
    calc ‖∑' s, term p γ s ζ‖ ≤ ∑' s, ‖term p γ s ζ‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' s, coefB p γ s / lowProd p S0 s / ‖mult p γ 0 ζ‖ :=
        hsumm.tsum_le_tsum hle (hsum.div_const _)
      _ = S / ‖mult p γ 0 ζ‖ := tsum_div_const
  have hsum1 : ∑' s, term p γ s ζ = -1 := by
    have : limFun p γ ζ = 1 + ∑' s, term p γ s ζ := rfl
    rw [this] at h0
    linear_combination h0
  rw [hsum1, norm_neg, norm_one] at hbound
  have : S / ‖mult p γ 0 ζ‖ < 1 := (div_lt_one hm0pos).mpr hm0
  linarith

/-- **Non-vanishing on the real segment.** For some `ρ ∈ [1/2, 1]`, `Λ(ρ) ≠ 0`. -/
theorem exists_real_limFun_ne_zero (hp0 : 0 < p) (hp2 : p < 1 / 2) (hγ : 0 < γ) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ 1 ∧ limFun p γ ρ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hball : ∀ z ∈ ball ((3 / 4 : ℝ) : ℂ) (1 / 4), 1 / 2 < z.re ∧ z.re < 1 := by
    intro z hz
    rw [mem_ball, dist_eq] at hz
    have h := abs_re_le_norm (z - ((3 / 4 : ℝ) : ℂ))
    rw [sub_re, ofReal_re] at h
    have h' := lt_of_le_of_lt h hz
    rw [abs_lt] at h'
    constructor <;> linarith [h'.1, h'.2]
  have hzero : ∀ z ∈ ball ((3 / 4 : ℝ) : ℂ) (1 / 4), z.im < 0 → limFun p γ z = 0 := by
    apply eqOn_zero_of_eq_zero_on_diameter
    · exact (continuousOn_limFun hp0 hp2 hγ).mono fun z hz =>
        mem_regionR.mpr ⟨(hball z hz.1).1.le, hz.2⟩
    · exact (differentiableOn_limFun hp0 hp2 hγ).mono fun z hz =>
        mem_regionV.mpr ⟨(hball z hz.1).1, hz.2⟩
    · intro z hz hzim
      have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzim])
      rw [hz']
      exact hcon z.re (hball z hz).1.le (hball z hz).2.le
  have han : AnalyticOnNhd ℂ (limFun p γ) regionV :=
    (differentiableOn_limFun hp0 hp2 hγ).analyticOnNhd isOpen_regionV
  set z₀ : ℂ := ((3 / 4 : ℝ) : ℂ) - ((1 / 8 : ℝ) : ℂ) * I with hz₀def
  have hre : (z₀ - ((3 / 4 : ℝ) : ℂ)).re = 0 := by simp [hz₀def]
  have him : (z₀ - ((3 / 4 : ℝ) : ℂ)).im = -(1 / 8) := by simp [hz₀def]
  have hz₀ball : z₀ ∈ ball ((3 / 4 : ℝ) : ℂ) (1 / 4) := by
    rw [mem_ball, dist_eq]
    have h := norm_le_abs_re_add_abs_im (z₀ - ((3 / 4 : ℝ) : ℂ))
    rw [hre, him, abs_zero, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at h
    linarith
  have hz₀im : z₀.im < 0 := by
    have : z₀.im = -(1 / 8) := by simp [hz₀def]
    rw [this]
    norm_num
  have hz₀V : z₀ ∈ regionV := mem_regionV.mpr ⟨(hball z₀ hz₀ball).1, hz₀im⟩
  have hev : limFun p γ =ᶠ[𝓝 z₀] 0 := by
    have hU : IsOpen (ball ((3 / 4 : ℝ) : ℂ) (1 / 4) ∩ {z : ℂ | z.im < 0}) :=
      isOpen_ball.inter (isOpen_lt continuous_im continuous_const)
    filter_upwards [hU.mem_nhds ⟨hz₀ball, hz₀im⟩] with z hz
    exact hzero z hz.1 hz.2
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_regionV hz₀V hev
  obtain ⟨ζ, hζV, hζ⟩ := exists_regionV_limFun_ne_zero hp0 hp2 hγ
  exact hζ (hall hζV)

end LastIterate
