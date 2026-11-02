"""Theorem LV (§6.6): certified upper bound for rho = sup E cos^4(pi w theta), w uniform in {1, ..., M}, over the minor
   region R_M = { 1/(2M) <= theta <= 1/2 - 1/(4M) } (and its mirror image), for every M >= 2.
   f(theta) = 3/8 + Re D(theta)/2 + Re D(2 theta)/8,  Re D(theta) = (1/M) sum_{j<=M} cos(2 pi j theta)
            = sin((2M+1) pi theta) / (2M sin(pi theta)) - 1/(2M).
   Certification for 2 <= M <= MMAX:
     |f'| <= (1/(2M)) sum 2 pi j + (1/(8M)) sum 4 pi j = 3 pi (M+1)/4, so on a grid of step h the supremum is at most
     the grid maximum + 3 pi (M+1) h / 8.  The grid covers the windows x = M theta in [1/2, X] and 1/2 - theta in
     [1/(4M), X/(2M)]; on the rest of R_M, using sin(pi t) >= 2t on [0, 1/2]:
       |Re D(theta)| <= 1/(4 M theta) + 1/(2M) <= 1/(4X) + 1/(2M),
       |Re D(2 theta)| <= 1/(4 M dist(2 theta, Z)) + 1/(2M) <= 1/(4X) + 1/(2M),
     so f <= 3/8 + (5/8)(1/(4X) + 1/(2M)) there.
   For M > MMAX: with x = M theta <= X, |Re D(theta) - sin(2 pi x)/(2 pi x)| <= C_X / M (bound printed below), and the
   limit function g(x) = 3/8 + sinc(2 pi x)/2 + sinc(4 pi x)/8 is certified on a grid in x with |g'| <= pi/2 + pi/4.
   Floating-point rounding (relative ~1e-15 per term) is far below the margins and is added as 1e-12.
   usage: python3 lv_rate_certified.py [MMAX]"""
import sys, math
import numpy as np
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2 ** 14
X = 10.0; TARGET = 0.446; ROUND = 1e-12

def ReD(theta, M):
    return np.sin((2 * M + 1) * np.pi * theta) / (2 * M * np.sin(np.pi * theta)) - 1 / (2 * M)

def f(theta, M):
    return 3 / 8 + ReD(theta, M) / 2 + ReD(2 * theta, M) / 8

def certify(M):
    L = 3 * np.pi * (M + 1) / 4
    h = 0.004 / L                       # grid error L h / 2 = 0.002
    lo, hi = 1 / (2 * M), 0.5 - 1 / (4 * M)
    wins = [(lo, min(hi, X / M)), (max(lo, 0.5 - X / (2 * M)), hi)]
    best = -1.0
    for a, b in wins:
        if b <= a: continue
        n = int(math.ceil((b - a) / h)) + 1
        t = np.linspace(a, b, n)
        best = max(best, float(f(t, M).max()))
    grid_bound = best + L * h / 2 + ROUND
    covered = X / M >= 0.5 - X / (2 * M)       # for M <= 1.5 X the two windows cover R_M
    rest = -1.0 if covered else 3 / 8 + (5 / 8) * (1 / (4 * X) + 1 / (2 * M))
    return max(grid_bound, rest), best

worst = 0.0; argworst = None
for M in range(2, MMAX + 1):
    b, raw = certify(M)
    if b > worst: worst, argworst = b, M
    if M in (2, 3, 8, 64, 1024, MMAX): print(f"M={M:6d}  grid max {raw:.5f}  certified sup <= {b:.5f}", flush=True)
print(f"2 <= M <= {MMAX}: certified rho <= {worst:.5f} (worst at M = {argworst})")

# M > MMAX.  Window x = M theta in [1/2, X]: with s(t) = sin(pi t)/(pi t) >= 1 - (pi t)^2/6,
#   |Re D(theta) - sinc(2 pi x)| <= 1/(2 M s(theta)) + (1/s(theta) - 1)/pi + 1/(2M), and the same with 2 theta, 2x.
# Mirror window theta = 1/2 - d, 2 d M in [1/2, X]: |Re D(theta)| <= 1/(2M cos(pi d)) + 1/(2M) and Re D(2 theta) = Re D(2d),
#   so f <= 3/8 + that/2 + (sinc(2 pi x') + err)/8 with x' = 2 d M, below the main window bound.
x = np.linspace(0.5, X, 2_000_001); hx = x[1] - x[0]
sinc = lambda y: np.sin(y) / y
g = 3 / 8 + sinc(2 * np.pi * x) / 2 + sinc(4 * np.pi * x) / 8
Lg = np.pi / 2 + np.pi / 4
gsup = float(g.max()) + Lg * hx / 2 + ROUND
M = MMAX + 1
def dR(t):
    st = 1 - (np.pi * t) ** 2 / 6
    return 1 / (2 * M * st) + (1 / st - 1) / np.pi + 1 / (2 * M)
err = dR(X / M) / 2 + dR(2 * X / M) / 8
mirror = 3 / 8 + (1 / (2 * M * np.cos(np.pi * X / (2 * M))) + 1 / (2 * M)) / 2 + (0.1284 + dR(X / M)) / 8
rest = 3 / 8 + (5 / 8) * (1 / (4 * X) + 1 / (2 * M))
print(f"M > {MMAX}: main window <= {gsup + err:.5f} (limit {gsup:.5f} + {err:.1e}), mirror <= {mirror:.5f}, rest <= {rest:.5f}")
total = max(worst, gsup + err, mirror, rest)
print(f"certified for all M >= 2: rho <= {total:.5f}   (target {TARGET}: {'OK' if total <= TARGET else 'FAIL'})")
print(f"rate: 5 ln 2 / -ln(sqrt(2) * {TARGET}) = {5 * math.log(2) / -math.log(math.sqrt(2) * TARGET):.4f}")
x2 = np.linspace(0.5, 3, 500001); print(f"(check: max sinc(2 pi x) on x >= 1/2 is {float(sinc(2*np.pi*x2).max()):.4f})")
