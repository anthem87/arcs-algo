"""Figure (§3.3, Lemma L and Table 1): the neighbourhood of an arc. For theta = a/q + X/N, the per-prime excess
   (1/pi(N)) sum_{p<=N} log|2 cos(pi p theta)| against the neighbourhood level A_q(X)/phi(q), with
   A_q(X) = (1/X) int_0^X log|Phi_q(-e(x))| dx (Lemma L: the prediction for large N). Left: the emerging arc 1/6
   (core 0.549, lobe 0.078). Right: the non-emerging arc 1/3 (core 0, the largest lobe, 0.1316 at X = 0.73).
   usage: python3 fig_lobes.py [N]"""
import sys, math
import numpy as np, matplotlib.pyplot as plt
from sympy import primerange, totient, cyclotomic_poly, Symbol, Poly
from figstyle import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
P = np.array(list(primerange(2, N + 1)), dtype=np.float64); n = len(P)
def excess(a, q, X):
    out = []
    for x in X:
        th = a / q + x / N; v = np.abs(2 * np.cos(np.pi * ((P * th) % 1.0)))
        out.append(np.log(np.maximum(v, 1e-300)).sum() / n)
    return np.array(out)
def A_over_phi(q, X):
    z = Symbol("z"); c = Poly(cyclotomic_poly(q, z), z).all_coeffs()[::-1]
    xs = np.linspace(0, X.max(), 200001); y = np.exp(2j * np.pi * xs) * -1
    h = np.log(np.abs(sum(ck * y**k for k, ck in enumerate(map(float, c)))) + 1e-300)
    H = np.concatenate([[0], np.cumsum((h[1:] + h[:-1]) / 2 * np.diff(xs))])
    with np.errstate(invalid="ignore", divide="ignore"):
        A = np.where(xs > 0, H / np.where(xs > 0, xs, 1), h[0])
    return np.interp(X, xs, A) / int(totient(q))
setup(); fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.8), sharey=True)
for ax, (a, q, title) in zip(axs, [(1, 6, "emerging arc 1/6"), (1, 3, "non-emerging arc 1/3")]):
    X = np.linspace(0, 3, 301)
    ax.plot(X, excess(a, q, X), color=BLUE, lw=1.2, label=f"primes ≤ {N:,}".replace(",", " "))
    ax.plot(X, A_over_phi(q, X), color=ORANGE, lw=1.2, ls="--", label=r"$A_q(X)/\varphi(q)$ (Lemma L)")
    ax.axhline(0, color=INK2, lw=0.8, ls=":"); ax.set_xlabel("X = N·(θ − a/q)"); ax.set_title(title, loc="left")
axs[0].set_ylabel("excess over the sea, per prime"); axs[0].legend(loc="upper right", fontsize=7.5)
save(fig, "fig_lobes")
