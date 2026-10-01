import Mathlib

namespace Arxiv.«1905.10899»

/-!
# ODE Analysis of Stochastic Gradient Methods with Optimism and Anchoring for Minimax Problems

*Reference:* [arxiv/1905.10899](https://arxiv.org/abs/1905.10899)
by *Ernest K. Ryu, Kun Yuan, Wotao Yin*
-/



variable (n m : ℕ)

abbrev E_n := EuclideanSpace ℝ (Fin n)
abbrev F_m := EuclideanSpace ℝ (Fin m)
abbrev Z_space := WithLp 2 (E_n n × F_m m)

noncomputable def toProd : Z_space n m ≃L[ℝ] (E_n n × F_m m) :=
  WithLp.prodContinuousLinearEquiv _ _ _ _

structure State where
  z       : Z_space n m
  z0      : Z_space n m   -- Anchor point (fixed throughout)
  t       : ℕ
  history : List (Z_space n m)

-- Operator G(z) = (∇_x L(z), -∇_y L(z))
noncomputable def F_operator
  (L : (Z_space n m) → ℝ)
  (z : Z_space n m) : Z_space n m :=
  let g := toProd n m (gradient L z)
  (toProd n m).symm (g.1, -g.2)

noncomputable def IsSaddlePoint (L : Z_space n m → ℝ) (z_star : Z_space n m) : Prop :=
  let (x_star, y_star) := toProd n m z_star
  (∀ y : F_m m, L ((toProd n m).symm (x_star, y)) ≤ L z_star) ∧
  (∀ x : E_n n, L z_star ≤ L ((toProd n m).symm (x, y_star)))

-- Anchored Simultaneous Gradient Descent
-- z_{t+1} = z_t - α_t * G(z_t) + β_t * (z_0 - z_t)
noncomputable def step
  (L : (Z_space n m) → ℝ)
  (s : State n m)
  (grad_coeff anchor_coeff : ℝ)
  : State n m :=

  -- Query gradient at current point
  let g := F_operator n m L s.z

  -- Compute gradient step
  let grad_step := grad_coeff • g

  -- Compute anchor step: pulls toward z_0
  let anchor_step := anchor_coeff • (s.z0 - s.z)

  -- Final update: z_{t+1} = z_t - grad_step + anchor_step
  let z_next := s.z - grad_step + anchor_step

  {
    s with
    z := z_next,
    z0 := s.z0,
    t := s.t + 1,
    history := s.history ++ [z_next]
  }

noncomputable def coefficients_schedule
  (gamma K : ℝ)
  (t : ℕ) : ℝ × ℝ :=
  (1 / (K * Real.sqrt ((t : ℝ) + gamma)), gamma / ((t : ℝ) + gamma))

noncomputable def coefficients_schedule_p
  (p gamma K : ℝ)
  (t : ℕ) : ℝ × ℝ :=
  ((1 - p) / (K * Real.rpow ((t : ℝ) + 1) p), (1 - p) * gamma / ((t : ℝ) + 1))


end Arxiv.«1905.10899»
