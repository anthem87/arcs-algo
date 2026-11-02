"""Theorem LV (§6.6): the rate rho = sup E cos^4(pi w theta) over the minor region 1/(2M) <= ||theta||, ||theta - 1/2|| >= 1/(4M),
   with E cos^4(pi w theta) = 3/8 + Re D(theta)/2 + Re D(2 theta)/8, D(theta) = E e(w theta), w uniform in {1, ..., M};
   and the limit M -> inf, where Re D(theta) -> sin(2 pi x)/(2 pi x), x = M theta.
   usage: python3 lv_rate.py"""
import numpy as np

def rho(M, N=400001):
    j = np.arange(1, M + 1); th = np.linspace(1 / (2 * M), 0.5 - 1 / (4 * M), N); best = 0.0
    for i in range(0, N, 20000):
        t = th[i:i + 20000]
        v = 3 / 8 + np.cos(2 * np.pi * np.outer(t, j)).mean(1) / 2 + np.cos(4 * np.pi * np.outer(t, j)).mean(1) / 8
        best = max(best, float(v.max()))
    return best

for M in (2, 3, 4, 8, 16, 64, 256, 1024, 2 ** 14): print(f"M={M:6d}  rho={rho(M):.5f}")
x = np.linspace(0.5, 20000, 40000001)
f = 3 / 8 + np.sin(2 * np.pi * x) / (2 * np.pi * x) / 2 + np.sin(4 * np.pi * x) / (4 * np.pi * x) / 8
print(f"limit: sup = {f.max():.5f} at x = M theta = {x[f.argmax()]:.4f};  sqrt(2) * 0.446 = {np.sqrt(2) * 0.446:.4f}")
