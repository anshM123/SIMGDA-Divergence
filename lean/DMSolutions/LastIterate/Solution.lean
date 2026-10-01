import DMSolutions.LastIterate.Dynamics

/-!
# Solution of `divergence_for_p_lt_half` (arXiv 1905.10899)

The statement is `Arxiv.«1905.10899».divergence_for_p_lt_half` from formal-conjectures pull
request 3675 (file `FormalConjectures/Arxiv/1905.10899/LastIterateConvergence.lean`, head
`d80f089b`). It is stated here verbatim, with the definitions of `Defs.lean`, which are a verbatim
copy of the definitions in that file.

The witness is `n' = m' = 1`, `K = 1`, `L(x, y) = ρ x y` (`LastIterate.gameL`) for a suitable
`ρ ∈ [1/2, 1]`, `z_star = 0`, and `z_init = (1, 0)`. In the complex coordinate `w = x + i y` the
iteration is `w_{t+1} = (1 - b_t + i ρ a_t) w_t + b_t`, with `a_t = (1 - p) (t + 1)^{-p}` and
`b_t = (1 - p) γ / (t + 1)`. Hence `w_t = Φ_t (1 + Σ_{s<t} b_s / Φ_{s+1})` with
`Φ_t = ∏_{s<t} (1 - b_s + i ρ a_s)`. Because `2p < 1`, `|Φ_t|` grows like `t^{1-2p}` and the
series converges to `Λ(ρ)`. The function `Λ` is holomorphic below the real axis, continuous up
to it, and not identically zero, so `Λ(ρ) ≠ 0` for some `ρ ∈ [1/2, 1]`
(`LastIterate.exists_real_limFun_ne_zero`). For this `ρ`, `‖F z_T‖ = ρ |w_T|` stays bounded
away from `0`, which rules out `‖F z_T‖² ≤ C / T`.
-/

namespace Arxiv.«1905.10899»

/-- `divergence_for_p_lt_half`, proved. -/
theorem divergence_for_p_lt_half_proved
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
  exact LastIterate.divergence_main p hp1 hp2 gamma h_gamma

end Arxiv.«1905.10899»
