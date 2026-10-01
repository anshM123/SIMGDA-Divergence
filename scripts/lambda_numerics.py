"""Numerical illustration (not part of the proof).

SimGD-A on L(x, y) = rho*x*y with K = 1 and z_0 = (1, 0) is, in complex form w = x + i y,
    w_{k+1} = m_k w_k + b_k,  w_0 = 1,  m_k = 1 - b_k + i rho a_k,
    a_k = (1 - p)(k + 1)^(-p),  b_k = (1 - p) gamma / (k + 1).
With Phi_k = prod_{s<k} m_s we have w_k = Phi_k (1 + sum_{s<k} b_s / Phi_{s+1}), and
    Lambda(rho) = 1 + sum_{s>=0} b_s / Phi_{s+1}
decides the behaviour: if Lambda(rho) != 0 then |w_k| grows like exp(kappa k^(1-2p)).
This script evaluates Lambda(rho) (terms are added while |Phi| < e^700; the rest is negligible)
and reports log10 |w_T|.

Usage: python lambda_numerics.py
"""
import cmath
import math


def run(p, gamma, rho, T):
    c = (1 - p) * gamma
    w = 1 + 0j
    log_phi = 0.0
    arg_phi = 0.0
    S = 1 + 0j
    for k in range(T):
        a = (1 - p) * (k + 1) ** (-p)
        b = c / (k + 1)
        m = complex(1 - b, rho * a)
        w = m * w + b
        log_phi += math.log(abs(m))
        arg_phi += cmath.phase(m)
        if log_phi < 700:
            S += b * cmath.exp(-complex(log_phi, arg_phi))
    return S, log_phi, w


def main():
    T = 400000
    for p, g in [(0.1, 2), (0.25, 2), (0.25, 5), (0.3, 2)]:
        for rho in (1.0, 0.5):
            S, lp, w = run(p, g, rho, T)
            lw = math.log10(abs(w)) if math.isfinite(abs(w)) else float("inf")
            print(f"p={p} gamma={g} rho={rho}: Lambda = {S.real:+.4f}{S.imag:+.4f}i, |Lambda| = {abs(S):.4f}, "
                  f"log|Phi_T| = {lp:.1f}, log10|w_T| = {lw:.1f}  (T = {T})", flush=True)


if __name__ == "__main__":
    main()
