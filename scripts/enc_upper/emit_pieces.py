import sympy as sp
from sym_all import d, n, e, r
from gen_fam import L, site_ops, MIN
from gen_pieces_data import reflected_origin, grade, C_of
from gen_fam2 import qr

HINTS = ("[_hnd, _hr, _hre, _hn, "
         "mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), "
         "mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), "
         "mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), "
         "mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), "
         "mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), "
         "mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), "
         "mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), "
         "mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), "
         "mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), "
         "mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), "
         "mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]")

def pair_s(v):
    if sp.expand(v[0]) == 0 and sp.expand(v[1]) == 0:
        return "((0 : ℤ), (0 : ℤ))"
    return f"({L(v[0])}, {L(v[1])})"

def table_index(orig, v):
    for i, t in enumerate(orig):
        if sp.simplify(t[0]-v[0]) == 0 and sp.simplify(t[1]-v[1]) == 0:
            return i
    raise ValueError("not in table")

def childC(m):
    return f"⟨{m} * n + r, {m} * d + e⟩"

def fracP(f):
    return "⟨n, d⟩" if f == 'P' else "⟨r, e⟩"

def dlstr(delta):
    return "1" if delta == 1 else "-1"

def emit_grades(m, delta, f):
    op, oq = site_ops(m, delta)
    orig = op if f == 'P' else oq
    s_ = 'p' if delta == 1 else 'n'
    out = []
    Cs = childC(m)
    Nc, Dc = C_of(m)
    for facet in ('t', 's'):
        vmin = orig[MIN[(m, delta, f, facet)]]
        for k, v in enumerate(orig):
            name = f"gr_{m}{s_}{f}_{k}_{facet}"
            if facet == 't':
                lhs = pair_s(vmin); rhs = pair_s(v)
                stmt = f"tCo {Cs} {lhs} ≤ tCo {Cs} {rhs}"
                diff = sp.expand(grade(m, v, 't') - grade(m, vmin, 't'))
            else:
                lhs = pair_s(vmin); rhs = pair_s(v)
                stmt = f"sCo {Cs} {lhs} ≤ sCo {Cs} {rhs}"
                diff = sp.expand(grade(m, v, 's') - grade(m, vmin, 's'))
            h = sp.expand(d*r - n*e - delta)
            qs, rem = sp.reduced(diff, [h], d, r, n, e, order='lex')
            q = sp.expand(qs[0]) if qs else sp.Integer(0); rem = sp.expand(rem)
            out.append(f"theorem {name} (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)")
            out.append(f"    (hdet : d * r - n * e = {dlstr(delta)}) : {stmt} := by")
            out.append(f"  have hq : (d * r - n * e - ({dlstr(delta)})) * ({L(q)}) = 0 := by")
            out.append(f"    rw [show d * r - n * e - ({dlstr(delta)}) = 0 by linarith only [hdet], zero_mul]")
            out.append(f"  have hg : 0 ≤ {L(rem)} := by nlinarith only {HINTS}")
            if facet == 't':
                out.append(f"  unfold tCo; dsimp only; linarith only [hq, hg]")
            else:
                out.append(f"  unfold sCo; dsimp only; linarith only [hq, hg]")
            out.append("")
    return out

if __name__ == "__main__":
    o = emit_grades(2, 1, 'P')
    print("\n".join(o[:12]))
