# Anchored simultaneous gradient descent diverges for step exponents below one half

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

Ryu, Yuan and Yin ([arXiv:1905.10899](https://arxiv.org/abs/1905.10899)) introduced anchored simultaneous gradient
descent (SimGD-A) for smooth convex–concave minimax problems:

```
z_{k+1} = z_k − α_k G(z_k) + β_k (z_0 − z_k),   α_k = (1 − p) / (K (k + 1)^p),   β_k = (1 − p) γ / (k + 1),
```

where `G(z) = (∇_x L(z), −∇_y L(z))`. They proved the last-iterate rate `‖G(z_k)‖² = O(k^{−(2−2p)})` for `p ∈ (1/2, 1)`. For
`p < 1/2`, their §4.2 says only: "Simple tests on bilinear examples show divergence when p < 1/2."

Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states the `p < 1/2`
question as the open theorem `Arxiv.«1905.10899».divergence_for_p_lt_half`. It is in pull request
[#3675](https://github.com/google-deepmind/formal-conjectures/pull/3675), in the file
`FormalConjectures/Arxiv/1905.10899/LastIterateConvergence.lean`. The same file contains the `p = 1/2` theorem of
Surina et al. ([arXiv:2604.03782](https://arxiv.org/abs/2604.03782)). The statement:

> for every `p ∈ (0, 1/2)` and `γ ≥ 2` there is a convex–concave problem (monotone `K`-Lipschitz operator, saddle
> point) and a run of SimGD-A on which `‖G(z_T)‖² ≤ C/T` fails for every `C > 0`.

**This repository proves it, with a Lean 4 proof of the exact statement.**

## Result

**Theorem.** Let `p ∈ (0, 1/2)`, `γ > 0`, `K > 0`, and let `L_ρ(x, y) = ρ x y` on `ℝ × ℝ` with `0 < ρ ≤ K`. Start SimGD-A at
`z_0 = (1, 0)`. Then for every `ρ` in an open dense subset of `(0, K]`, `‖G(z_k)‖` grows like `exp(κ k^{1−2p})`.

- **Reduction.** In complex form, `w_{k+1} = m_k w_k + b_k` with `w_0 = 1` and `m_k = 1 − b_k + i ρ a_k`. Hence
  `w_k = Φ_k (1 + Σ_{s<k} b_s / Φ_{s+1})`, where `Φ_k = ∏_{s<k} m_s`.
- **Growth.** Since `2p < 1`, `|Φ_k|` grows like `exp(κ k^{1−2p})`. So the series converges to a constant `Λ(ρ)`.
  - If `Λ(ρ) ≠ 0`, the method diverges.
  - If `Λ(ρ) = 0`, the iterates converge, so an existence argument is needed.
- **Non-vanishing.** `Λ` extends holomorphically to the lower half-plane, is continuous up to the real axis, and is not
  identically zero there. Extending by `0` above the axis and applying Morera's theorem and the identity theorem then
  shows that `Λ` cannot vanish on any real interval.

## Lean 4 verification (`lean/`)

All files import Mathlib only (and each other).

| File | Contents |
|---|---|
| `Defs.lean` | the definitions of the pull-request file, verbatim (`Z_space`, `toProd`, `State`, `F_operator`, `IsSaddlePoint`, `step`, `coefficients_schedule_p`, …) |
| `Uniqueness.lean` | boundary uniqueness: a function continuous on a closed lower half-disk, holomorphic inside and zero on the diameter vanishes (`LastIterate.eqOn_zero_of_eq_zero_on_diameter`) |
| `Growth.lean` | lower bounds for `|Φ_k(ζ)|` on the region `Re ζ ≥ 1/2`, `Im ζ ≤ 0`, and summability |
| `Analytic.lean` | `Λ` is continuous and holomorphic, and `Λ(ρ) ≠ 0` for some `ρ ∈ [1/2, 1]` (`LastIterate.exists_real_limFun_ne_zero`) |
| `Dynamics.lean` | the game `L(x, y) = ρ x y`: gradient, monotonicity, Lipschitz bound, saddle point, the complex form of the iteration, and the failure of the rate |
| `Solution.lean` | `Arxiv.«1905.10899».divergence_for_p_lt_half_proved`, whose statement is that of `divergence_for_p_lt_half` verbatim |
| `CheckAnswer.lean` | restates `divergence_for_p_lt_half` under its own name, proves it, checks the two types are equal by `rfl`, and prints the axioms |

- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `admit`, `native_decide` or `axiom`.
- **Verbatim check:** `scripts/check_verbatim.py` compares `Defs.lean`, `Solution.lean` and `CheckAnswer.lean` with
  `lean/reference/LastIterateConvergence.pr3675.lean`. That file is the pull-request file at head `d80f089b`, git blob
  `a352fef4`. Log: `logs/check_verbatim.log`.
- **Lean version:** the pull request was written for Lean v4.27, whose repository import path no longer exists. The
  definitions and the statement compile unchanged against current Mathlib.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

Log: `logs/lean_check.log` (exit 0, 178 s).

## Numerical illustration (`scripts/lambda_numerics.py`, `logs/lambda_numerics.log`)

`Λ(1)` and `Λ(1/2)` for several `(p, γ)`. All values are nonzero, e.g. `Λ(1) = −0.0654 − 0.0579i` at `p = 0.25`, `γ = 2`. The iterate reaches
`|w_k| ≈ 10^145` at `k = 4·10^5`. For `p` close to `1/2` the growth starts only after very many iterations.

## Prior work

- The question is the remark in §4.2 of Ryu–Yuan–Yin. It is stated as open in Formal Conjectures pull request #3675.
- Surina et al. (2026) proved the rate `O(1/k)` for `p = 1/2`.
- Search date 2026-10-01. We found no treatment of `p < 1/2` in:
  - arXiv:1905.10899 v3;
  - arXiv:2604.03782;
  - the 46 works citing arXiv:1905.10899 (Semantic Scholar);
  - Formal Conjectures issues and pull requests, including the "open statements with known solutions" issues;
  - GitHub repository search;
  - web search.
