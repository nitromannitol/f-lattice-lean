"""The chain reflection of the strong estimates (task 49, I3 bridge): with R' = centre of the frame of u (Lean
ChildFrame.centre = kernel + transverse + (1, −1)) and w' = η σ − v (chainSheet η z = F(z + ησ − v) + ε a·(z + ησ)), the reflection
σ(ξ) = R − w' − ξ with R = C (or R = C + I, I = (1, −1)) is tested on the 36 proper words and both phases η = ±1:
  (i)  the reflected F2F3 policy refl(c, i) = pol_F(σ c, σ i) is a quota policy of h_η (black: both inputs, white: one), and
       Φ_η is nondecreasing along it;
  (ii) the chain policy pol_F itself makes h_η nondecreasing along it (so that F2F4 holds with chainPolicy = pol_F).
pol_F is the F2F3 policy: maximal admissible pairs (i input of c with Φ_η(i) ≤ Φ_η(c)), as in phase_policy_check.py.
Parts (i) and (ii) are per-pair conditions over the centres of a box; they are checked exactly.
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_tile_check as otc  # noqa: E402
import phase_policy_check as ppc  # noqa: E402

ns = otc.load_proto()
standard, Frame = ns["standard"], ns["Frame"]
inc_neg, inc_pos = ppc.inc_neg, ppc.inc_pos
words = ppc.words
BOX = 5
CENTRES = ppc.CENTRES
I = (1, -1)


def setup(u, eta):
    F = standard(tuple(u))[0]
    fr = Frame(list(u))
    N, D, eps = fr.N, fr.D, fr.eps
    n_, d_ = fr.n, fr.d
    C = (d_ + (n_ - d_) + 1, n_ + (n_ + d_) - 1)  # kernel (mu = 1, child even) + transverse + (1, −1)
    sig = (2 * eps * D, 2 * eps * N)
    v = (eps * (N - D), eps * (N + D))
    a = (N, -D)
    cache = {}

    def Fc(z):
        if z not in cache:
            cache[z] = F(z)
        return cache[z]

    def P(y):
        return Fc(y) - Fc((y[0] - v[0], y[1] - v[1])) - eps * (a[0] * y[0] + a[1] * y[1])

    def Phi(z):
        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
        return Fc(z) - Fc(zs) + P(zs)

    def h(z):
        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
        return Fc((zs[0] - v[0], zs[1] - v[1])) + eps * (a[0] * zs[0] + a[1] * zs[1])

    def lap_h(c):
        return (h(inc_neg(c)) - h(c)) + (h(inc_pos(c)) - h(c))

    wp = (eta * sig[0] - v[0], eta * sig[1] - v[1])  # w' = ησ − v
    return dict(F=F, C=C, wp=wp, Phi=Phi, h=h, lap_h=lap_h, sig=sig, v=v, eps=eps, N=N, D=D)


def pol_F(S, p, q):
    """The F2F3 policy (admissible pairs): q an input of p with Φ(q) ≤ Φ(p)."""
    return (q == inc_neg(p) or q == inc_pos(p)) and S["Phi"](q) <= S["Phi"](p)


def test(u, eta, R):
    S = setup(u, eta)
    Phi, h, lap_h, wp = S["Phi"], S["h"], S["lap_h"], S["wp"]

    def sigma(x):
        return (R[0] - wp[0] - x[0], R[1] - wp[1] - x[1])

    def refl(c, i):
        return pol_F(S, sigma(c), sigma(i))

    # (i) quota of h_η on the reflected policy, and Φ nondecreasing along it
    quota_ok = True
    for c in CENTRES:
        L = lap_h(c)
        if L not in (-1, 0):
            continue
        adm = [i for i in (inc_neg(c), inc_pos(c)) if refl(c, i)]
        if (L == -1 and len(adm) < 2) or (L == 0 and len(adm) < 1):
            quota_ok = False
            break
    phi_ok = True
    for c in CENTRES:
        # all pairs (c, i) with refl(c, i): i = σ(input of σc)
        sc = sigma(c)
        for q in (inc_neg(sc), inc_pos(sc)):
            i = sigma(q)
            if pol_F(S, sc, q) and not (Phi(c) <= Phi(i)):
                phi_ok = False
                break
        if not phi_ok:
            break
    # (ii) h nondecreasing along pol_F pairs
    h_ok = True
    for p in CENTRES:
        for q in (inc_neg(p), inc_pos(p)):
            if pol_F(S, p, q) and not (h(p) <= h(q)):
                h_ok = False
                break
        if not h_ok:
            break
    return quota_ok, phi_ok, h_ok


if __name__ == "__main__":
    tallies = {}
    for u in words:
        row = []
        for eta in (1, -1):
            S = setup(u, eta)
            for label, R in [("R=C", S["C"]), ("R=C+I", (S["C"][0] + I[0], S["C"][1] + I[1]))]:
                q, p, hh = test(u, eta, R)
                tallies.setdefault((eta, label), [0, 0, 0, 0])
                t = tallies[(eta, label)]
                t[0] += q; t[1] += p; t[2] += hh; t[3] += (q and p and hh)
                row.append(f"eta={eta:+d} {label}: quota {int(q)} Φnondec {int(p)} hmono {int(hh)}")
        print(u, " | ".join(row), flush=True)
    print("tallies (quota ok, Φ nondecreasing ok, h monotone ok, all three) over", len(words), "words:")
    for k in sorted(tallies):
        print("  ", k, tallies[k])
