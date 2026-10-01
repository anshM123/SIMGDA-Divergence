import Mathlib

/-!
# Boundary uniqueness on a half-disk

Let `D` be an open disk with centre on the real axis. A function that is continuous on the
closed lower half of `D`, complex differentiable on the open lower half, and zero on the real
diameter vanishes on the open lower half of `D`.

The proof extends the function by zero to the upper half of `D`. The extension is continuous on
`D`, and its integral around every rectangle in `D` vanishes: a rectangle on one side of the real
axis is covered by the Cauchy-Goursat theorem, and a rectangle that crosses the axis is cut into
two such rectangles. Morera's theorem makes the extension holomorphic on `D`, and the identity
theorem makes it zero.
-/

namespace LastIterate

open Complex Metric Set Filter Topology intervalIntegral
open scoped Interval

/-- The integral of `g` around the boundary of the rectangle with opposite corners `z` and `w`. -/
noncomputable def rectIntegral (g : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, g (z.re + y * I))

/-- The rectangle integral vanishes for a function that is continuous on the closed rectangle
and holomorphic on its interior. -/
theorem rectIntegral_eq_zero {g : ℂ → ℂ} {z w : ℂ} (hc : ContinuousOn g (Rectangle z w))
    (hd : DifferentiableOn ℂ g
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    rectIntegral g z w = 0 :=
  integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g z w hc hd

/-- Cutting a rectangle along the real axis. -/
theorem rectIntegral_split {g : ℂ → ℂ} {z w : ℂ} (hc : ContinuousOn g (Rectangle z w))
    (h0 : (0 : ℝ) ∈ [[z.im, w.im]]) :
    rectIntegral g z w = rectIntegral g z ⟨w.re, 0⟩ + rectIntegral g ⟨z.re, 0⟩ w := by
  have hvert : ∀ x ∈ [[z.re, w.re]],
      IntervalIntegrable (fun y : ℝ => g (x + y * I)) MeasureTheory.volume z.im w.im := by
    intro x hx
    refine ContinuousOn.intervalIntegrable ?_
    refine hc.comp (by fun_prop) ?_
    intro y hy
    rw [Rectangle, mem_reProdIm]
    simpa using And.intro hx hy
  have hsplit : ∀ x ∈ [[z.re, w.re]],
      ∫ y : ℝ in z.im..w.im, g (x + y * I) =
        (∫ y : ℝ in z.im..0, g (x + y * I)) + ∫ y : ℝ in (0 : ℝ)..w.im, g (x + y * I) := by
    intro x hx
    rw [integral_add_adjacent_intervals]
    · exact (hvert x hx).mono_set (uIcc_subset_uIcc left_mem_uIcc h0)
    · exact (hvert x hx).mono_set (uIcc_subset_uIcc h0 right_mem_uIcc)
  simp only [rectIntegral]
  rw [hsplit w.re right_mem_uIcc, hsplit z.re left_mem_uIcc]
  simp only [smul_eq_mul]
  ring

/-- **Boundary uniqueness on a half-disk.** -/
theorem eqOn_zero_of_eq_zero_on_diameter {c r : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (ball (c : ℂ) r ∩ {z | z.im ≤ 0}))
    (hd : DifferentiableOn ℂ f (ball (c : ℂ) r ∩ {z | z.im < 0}))
    (h0 : ∀ z ∈ ball (c : ℂ) r, z.im = 0 → f z = 0) :
    ∀ z ∈ ball (c : ℂ) r, z.im < 0 → f z = 0 := by
  classical
  -- the extension by zero
  set g : ℂ → ℂ := fun z => if z.im ≤ 0 then f z else 0 with hg
  have hclosed : IsClosed {u : ℂ | u.im ≤ 0} := isClosed_le continuous_im continuous_const
  have g_cont : ContinuousOn g (ball (c : ℂ) r) := by
    rw [hg]
    refine ContinuousOn.if ?_ ?_ continuousOn_const
    · rintro a ⟨ha, hfr⟩
      rw [frontier_setOfPred_im_le] at hfr
      exact h0 a ha hfr
    · refine hc.mono ?_
      rintro a ⟨ha, hcl⟩
      exact ⟨ha, hclosed.closure_subset hcl⟩
  have g_lower : DifferentiableOn ℂ g (ball (c : ℂ) r ∩ {z | z.im < 0}) := by
    refine hd.congr fun z hz => ?_
    have hz' : z.im ≤ 0 := le_of_lt hz.2
    simp only [hg, if_pos hz']
  have g_upper : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := by
    refine (differentiableOn_const (0 : ℂ)).congr fun z hz => ?_
    have hz' : ¬ z.im ≤ 0 := not_le.mpr hz
    simp only [hg, if_neg hz']
  -- rectangles on one side of the real axis
  have rect_side : ∀ z w : ℂ, Rectangle z w ⊆ ball (c : ℂ) r →
      (max z.im w.im ≤ 0 ∨ 0 ≤ min z.im w.im) → rectIntegral g z w = 0 := by
    intro z w hzw hside
    refine rectIntegral_eq_zero (g_cont.mono hzw) ?_
    rcases hside with h | h
    · refine g_lower.mono fun u hu => ⟨hzw ?_, ?_⟩
      · rw [mem_reProdIm] at hu
        rw [Rectangle, mem_reProdIm, ← Icc_min_max, ← Icc_min_max]
        exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩
      · rw [mem_reProdIm] at hu
        exact lt_of_lt_of_le hu.2.2 h
    · refine g_upper.mono fun u hu => ?_
      rw [mem_reProdIm] at hu
      exact lt_of_le_of_lt h hu.2.1
  -- all rectangles
  have rect_all : ∀ z w : ℂ, Rectangle z w ⊆ ball (c : ℂ) r → rectIntegral g z w = 0 := by
    intro z w hzw
    by_cases hside : max z.im w.im ≤ 0 ∨ 0 ≤ min z.im w.im
    · exact rect_side z w hzw hside
    push Not at hside
    have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
      rw [← Icc_min_max]
      exact ⟨hside.2.le, hside.1.le⟩
    have sub1 : Rectangle z ⟨w.re, 0⟩ ⊆ Rectangle z w := by
      intro u hu
      rw [Rectangle, mem_reProdIm] at hu ⊢
      exact ⟨hu.1, uIcc_subset_uIcc left_mem_uIcc h0mem hu.2⟩
    have sub2 : Rectangle ⟨z.re, 0⟩ w ⊆ Rectangle z w := by
      intro u hu
      rw [Rectangle, mem_reProdIm] at hu ⊢
      exact ⟨hu.1, uIcc_subset_uIcc h0mem right_mem_uIcc hu.2⟩
    have side1 : max z.im (⟨w.re, 0⟩ : ℂ).im ≤ 0 ∨ 0 ≤ min z.im (⟨w.re, 0⟩ : ℂ).im := by
      rcases le_total z.im 0 with h | h
      · exact Or.inl (max_le h le_rfl)
      · exact Or.inr (le_min h le_rfl)
    have side2 : max (⟨z.re, 0⟩ : ℂ).im w.im ≤ 0 ∨ 0 ≤ min (⟨z.re, 0⟩ : ℂ).im w.im := by
      rcases le_total w.im 0 with h | h
      · exact Or.inl (max_le le_rfl h)
      · exact Or.inr (le_min le_rfl h)
    rw [rectIntegral_split (g_cont.mono hzw) h0mem, rect_side _ _ (sub1.trans hzw) side1,
      rect_side _ _ (sub2.trans hzw) side2, add_zero]
  have g_cons : IsConservativeOn g (ball (c : ℂ) r) := by
    intro z w hzw
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    exact rect_all z w hzw
  have g_diff : DifferentiableOn ℂ g (ball (c : ℂ) r) :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).mp ⟨g_cons, g_cont⟩
  intro z hz hzim
  have hr : 0 < r := pos_of_mem_ball hz
  set z₀ : ℂ := (c : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hz₀def
  have hz₀ : z₀ ∈ ball (c : ℂ) r := by
    rw [mem_ball, dist_eq, hz₀def, add_sub_cancel_left]
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]
    linarith
  have hev : g =ᶠ[𝓝 z₀] 0 := by
    have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_lt continuous_const continuous_im
    have hmem : z₀ ∈ {u : ℂ | 0 < u.im} := by
      show 0 < z₀.im
      simp only [hz₀def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add, add_zero]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with u hu
    have hu' : ¬ u.im ≤ 0 := not_le.mpr hu
    simp only [hg, if_neg hu', Pi.zero_apply]
  have hzero := (g_diff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hz₀ hev hz
  have hgz : g z = f z := by
    simp only [hg, if_pos hzim.le]
  rw [← hgz]
  exact hzero

end LastIterate
