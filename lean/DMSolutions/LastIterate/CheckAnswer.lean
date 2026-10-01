import DMSolutions.LastIterate.Solution

/-!
# Checks for the solution of `divergence_for_p_lt_half`

The theorem below has the name and the statement of the repository theorem
`Arxiv.«1905.10899».divergence_for_p_lt_half`, copied verbatim, and is proved by
`divergence_for_p_lt_half_proved`. The `example` checks that the two types are definitionally
equal.
-/

namespace Arxiv.«1905.10899»

theorem divergence_for_p_lt_half
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
  exact divergence_for_p_lt_half_proved p hp1 hp2 gamma h_gamma

example : type_of% @divergence_for_p_lt_half = type_of% @divergence_for_p_lt_half_proved := rfl

end Arxiv.«1905.10899»

#print axioms Arxiv.«1905.10899».divergence_for_p_lt_half_proved
#print axioms Arxiv.«1905.10899».divergence_for_p_lt_half
