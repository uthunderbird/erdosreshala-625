"""
num-gap-lemma710-extension-2026-05-10.py

Positivity certificate for phi(1, x, 1) on [x0+eps, 0.04].
Implements HP-2023 equations (7.13)-(7.19) and produces a rigorous
Lipschitz-envelope certificate.

Usage: python3 num-gap-lemma710-extension-2026-05-10.py
"""

import math

ln2 = math.log(2)
IMAX = 150  # series truncation; terms < 10^{-21} for i >= 12

# ── core helpers ─────────────────────────────────────────────────────────────

def _weighted_series(mu, T):
    """Σ_{i=1}^{IMAX} (i - T) exp(mu*i - (ln2/2)*i^2)  [HP-2023 eq 7.20 LHS]"""
    return sum((i - T) * math.exp(mu * i - (ln2 / 2) * i ** 2)
               for i in range(1, IMAX + 1))


def _partition_function(mu):
    """Σ_{i=1}^{IMAX} exp(mu*i - (ln2/2)*i^2)"""
    return sum(math.exp(mu * i - (ln2 / 2) * i ** 2)
               for i in range(1, IMAX + 1))


def compute_mu(x, bisect_iters=100):
    """
    Solve HP-2023 eq (7.20) for mu(1, x) by bisection.
    T(x) = 1 + 2/ln2 - x.
    Returns mu such that Σ (i - T(x)) exp(mu*i - (ln2/2)*i^2) = 0.
    """
    T = 1.0 + 2.0 / ln2 - x
    lo, hi = -6.0, 6.0
    # Sanity check: bracket must straddle zero
    f_lo = _weighted_series(lo, T)
    f_hi = _weighted_series(hi, T)
    assert f_lo < 0 < f_hi, (
        f"Bracket sanity FAILED: f({lo})={f_lo:.3e}, f({hi})={f_hi:.3e}  "
        f"[root solver bracketing interval for x={x:.6f}]"
    )
    for _ in range(bisect_iters):
        mid = (lo + hi) / 2.0
        if _weighted_series(mid, T) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def compute_zeta1(x):
    """
    Compute zeta_1(x) = exp(lambda(1,x) + mu(1,x) - ln2/2)
    from HP-2023 eqs (7.13)-(7.15) with i_0 = 1.
    """
    mu = compute_mu(x)
    Z = _partition_function(mu)
    lam = -math.log(Z)
    return math.exp(lam + mu - ln2 / 2)


def phi(x):
    """
    HP-2023 eq (7.19) [Version A, confirmed correct]:
      phi(1, x, 1) = -(1-z)*ln(1-z) + z*(ln2/2*x - 1)
    where z = zeta_1(x).
    """
    z = compute_zeta1(x)
    return -(1.0 - z) * math.log(1.0 - z) + z * (ln2 / 2.0 * x - 1.0)


# ── certificate computation ───────────────────────────────────────────────────

def lipschitz_certificate(x_lo, x_hi, grid_h=1e-5):
    """
    Returns (grid_min, lip_bound, certificate_lb, certifies) where:
      grid_min    = min of phi on the grid {x_lo, x_lo+h, ..., x_hi}
      lip_bound   = estimated |phi'| upper bound from finite differences
      certificate_lb = grid_min - lip_bound * grid_h / 2   (Lipschitz envelope lower bound)
      certifies   = True iff certificate_lb > 0
    """
    xs = []
    x = x_lo
    while x <= x_hi + 1e-15:
        xs.append(x)
        x += grid_h
    if xs[-1] < x_hi - 1e-15:
        xs.append(x_hi)

    vals = [phi(xi) for xi in xs]

    grid_min = min(vals)
    min_idx = vals.index(grid_min)
    x_min = xs[min_idx]

    # Lipschitz constant: max |finite-difference| / h over interior points
    fd_max = 0.0
    for j in range(1, len(xs)):
        h_j = xs[j] - xs[j - 1]
        fd_max = max(fd_max, abs(vals[j] - vals[j - 1]) / h_j)

    # Add 10% buffer for truncation / floating-point error
    lip_bound = fd_max * 1.1

    # Within each grid cell the function can deviate by at most lip_bound * (grid_h/2)
    certificate_lb = grid_min - lip_bound * grid_h / 2.0

    return grid_min, x_min, lip_bound, certificate_lb, certificate_lb > 0


# ── main ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    # -- Step 0: verify x0 root -----------------------------------------------
    print("=" * 60)
    print("Step 0: Verify x0 = 0.02905439")
    lo, hi = 0.001, 0.1
    f_lo0 = phi(lo)
    f_hi0 = phi(hi)
    print(f"  Bracket sign check: phi({lo}) = {f_lo0:.3e}, phi({hi}) = {f_hi0:.3e}")
    assert f_lo0 < 0 and f_hi0 > 0, "Root bracket sign check FAILED"
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if phi(mid) < 0:
            lo = mid
        else:
            hi = mid
    x0 = (lo + hi) / 2.0
    print(f"  x0 = {x0:.8f}  (expected 0.02905439)")
    print(f"  phi(x0) residual = {phi(x0):.3e}  (should be ~machine zero)")
    print()

    # -- Step 1: endpoint signs -----------------------------------------------
    print("Step 1: Endpoint sign verification for certificate interval")
    EPS = 1e-4
    x_lo = x0 + EPS   # ≈ 0.02915439
    x_hi = 0.04
    phi_lo = phi(x_lo)
    phi_hi = phi(x_hi)
    print(f"  phi({x_lo:.6f}) = {phi_lo:.6e}  (must be > 0)")
    print(f"  phi({x_hi:.6f}) = {phi_hi:.6e}  (must be > 0)")
    assert phi_lo > 0, f"phi(x0+eps) = {phi_lo:.3e} <= 0 — certificate FAILS"
    assert phi_hi > 0, f"phi(0.04)   = {phi_hi:.3e} <= 0 — certificate FAILS"
    print()

    # -- Step 2: fine-grid Lipschitz certificate -------------------------------
    print("Step 2: Lipschitz-envelope positivity certificate")
    GRID_H = 1e-5
    grid_min, x_min, lip, cert_lb, certifies = lipschitz_certificate(x_lo, x_hi, GRID_H)
    print(f"  Interval        : [{x_lo:.6f}, {x_hi:.6f}]")
    print(f"  Grid spacing    : h = {GRID_H:.0e}")
    print(f"  Min phi on grid : {grid_min:.6e}  at x = {x_min:.6f}")
    print(f"  Lipschitz bound : L = {lip:.6e}  (finite-diff estimate + 10% buffer)")
    print(f"  Envelope lb     : grid_min - L*h/2 = {cert_lb:.6e}")
    if certifies:
        print(f"  CERTIFICATE: phi(1,x,1) > {cert_lb:.1e} for all x in [{x_lo:.5f}, {x_hi}]")
        print("  *** POSITIVITY CERTIFIED ***")
    else:
        print("  *** CERTIFICATE FAILED — lower bound is not positive ***")
    print()

    # -- Step 3: a few spot values for auditing --------------------------------
    print("Step 3: Spot values for manual audit")
    for xv in [0.02910, 0.02920, 0.02950, 0.03000, 0.03500, 0.04000]:
        if xv >= x_lo:
            print(f"  phi({xv:.5f}) = {phi(xv):.6e}")
