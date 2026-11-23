import sys
import sympy as sp
from sym_all import d, n, e, r
from gen_fam import L, site_ops, MIN
from gen_pieces_data import reflected_origin, C_of
from emit_pieces import emit_grades, pair_s, table_index
from gen_fam import L as _L

def fname(m, delta, f): return f"fam_{f}{m}{'p' if delta == 1 else 'n'}"
def gname(m, delta, f, k, facet): return f"gr_{m}{'p' if delta == 1 else 'n'}{f}_{k}_{facet}"
def pname(m, delta, f, j): return f"pc_{m}{'p' if delta == 1 else 'n'}{f}_{j}"
def Cs(m): return f"⟨{m} * n + r, {m} * d + e⟩"

def emit_pieces(m, delta):
    op, oq = site_ops(m, delta)
    out = []
    for f, orig in (('P', op), ('Q', oq)):
        F = "⟨n, d⟩" if f == 'P' else "⟨r, e⟩"
        for j, v in enumerate(orig):
            vr = reflected_origin(m, delta, f, v)
            vr = (sp.expand(vr[0]), sp.expand(vr[1]))
            k = table_index(orig, vr)
            V = pair_s(v); Vr = pair_s(vr)
            VT = pair_s(orig[MIN[(m, delta, f, 't')]]); VS = pair_s(orig[MIN[(m, delta, f, 's')]])
            C = Cs(m)
            name = pname(m, delta, f, j); fam = fname(m, delta, f)
            dl = '1' if delta == 1 else '-1'
            out.append(f"theorem {name} (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)")
            out.append(f"    (hdet : d * r - n * e = {dl}) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :")
            out.append(f"    ∀ w : ℤ × ℤ, InH {F} w → InH {C} ({V} + w) := by")
            out.append(f"  have hμC : muOf {C} = {'2' if m == 1 else '1'} := by")
            out.append(f"    apply {'muOf_mk_two' if m == 1 else 'muOf_mk_one'}; omega")
            if f == 'P':
                out.append(f"  have hμF : muOf {F} = 2 := muOf_mk_two n d (by omega)")
            else:
                out.append(f"  have hμF : muOf {F} = 1 := muOf_mk_one r e (by omega)")
            out.append(f"  have hvev : (({L(v[0])} : ℤ) + ({L(v[1])} : ℤ)) % 2 = 0 := by omega")
            out.append(f"  have hvrev : (({L(vr[0])} : ℤ) + ({L(vr[1])} : ℤ)) % 2 = 0 := by omega")
            fam_call = f"(fun w hw => {fam} n d e r hn hnd hr hre hdet hodd heven w hw)"
            gt_j = gname(m, delta, f, j, 't'); gs_j = gname(m, delta, f, j, 's')
            gt_k = gname(m, delta, f, k, 't'); gs_k = gname(m, delta, f, k, 's')
            out.append(f"  exact piece_sub {C} {F} {V} {Vr}")
            out.append(f"    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)")
            out.append(f"    (lowOK_origin {C} {F} {V} {VT} {VS} hvev ({gt_j} n d e r hn hnd hr hre hdet) ({gs_j} n d e r hn hnd hr hre hdet) {fam_call})")
            out.append(f"    (lowOK_origin {C} {F} {Vr} {VT} {VS} hvrev ({gt_k} n d e r hn hnd hr hre hdet) ({gs_k} n d e r hn hnd hr hre hdet) {fam_call})")
            out.append("")
    return out

def emit_grades_all():
    out = []
    for m in (1, 2):
        for dl in (1, -1):
            for f in 'PQ':
                out += emit_grades(m, dl, f)
    return out

# the membership shape of each flag, in the order of the definitions: (kind, f, origin index)
# kind: 'z' (unshifted, origin 0) or 's' (shiftS with the given expression)
DEFS = {
 ('even', 1): [('z','Q',0), ('s','Q','texV1Odd ⟨n, d⟩ + (texV2 ⟨n, d⟩ + texV2 ⟨n, d⟩)',1),
               ('s','P','texV1Even ⟨r, e⟩',0), ('s','P','texV1Even ⟨r, e⟩ + texV2 ⟨n, d⟩',1),
               ('s','P','texV2 ⟨r, e⟩',2), ('s','P','texV2 ⟨r, e⟩ + texV2 ⟨n, d⟩',3)],
 ('even', -1): [('s','Q','texV1Odd ⟨n, d⟩',0), ('s','Q','texV2 ⟨n, d⟩ + texV2 ⟨n, d⟩',1),
               ('z','P',0), ('s','P','texV2 ⟨n, d⟩',1),
               ('s','P','texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩',2), ('s','P','texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩ + texV2 ⟨n, d⟩',3)],
 ('odd', 1): [('z','Q',0), ('s','Q','texV1Even ⟨r, e⟩',1),
              ('s','Q','texV1Odd ⟨n, d⟩ + texV2 ⟨n, d⟩',2), ('s','Q','texV1Odd ⟨n, d⟩ + texV2 ⟨n, d⟩ + texV1Even ⟨r, e⟩',3),
              ('s','P','texV1Even ⟨r, e⟩ + texV1Even ⟨r, e⟩',0), ('s','P','texV2 ⟨r, e⟩',1)],
 ('odd', -1): [('s','Q','texV1Odd ⟨n, d⟩',0), ('s','Q','texV1Odd ⟨n, d⟩ + texV1Even ⟨r, e⟩',1),
               ('s','Q','texV2 ⟨n, d⟩',2), ('s','Q','texV2 ⟨n, d⟩ + texV1Even ⟨r, e⟩',3),
               ('z','P',0), ('s','P','texV1Even ⟨r, e⟩ + texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩',1)],
}

def emit_final(kind, delta):
    m = 2 if kind == 'even' else 1
    lem = f"enc{'Even' if kind == 'even' else 'Odd'}_{'F' if delta == 1 else 'T'}"
    flag = 'false' if delta == 1 else 'true'
    tgt = "⟨2 * n + r, 2 * d + e⟩" if kind == 'even' else "⟨1 * n + r, 1 * d + e⟩"
    fl = 'Odd' if kind == 'odd' else 'Even'
    chS = f"{kind}ChildS {flag} (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩"
    out = []
    out.append(f"theorem {lem} (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)")
    out.append(f"    (hdet : d * r - n * e = {'1' if delta == 1 else '-1'}) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :")
    out.append(f"    {chS} ⊆ HSet {tgt} := by")
    out.append(f"  intro z hz")
    out.append(f"  simp only [{kind}ChildS, Set.mem_union] at hz")
    pat = "((((h0 | h1) | h2) | h3) | h4) | h5"
    out.append(f"  rcases hz with {pat}")
    items = DEFS[(kind, delta)]
    for i, it in enumerate(items):
        h = f"h{i}"
        if it[0] == 'z':
            _, f, j = it
            pn = pname(m, delta, f, j)
            out.append(f"  · exact mem_zero_piece _ _ ({pn} n d e r hn hnd hr hre hdet hodd heven) z {h}")
        else:
            _, f, expr, j = it
            pn = pname(m, delta, f, j)
            _op, _oq = site_ops(m, delta)
            v = (_op if f == 'P' else _oq)[j]
            used = [nm for nm in ('texV1Odd', 'texV1Even', 'texV2') if nm in expr]
            defform = {'texV1Odd ⟨n, d⟩': '(2*d,2*n)', 'texV1Even ⟨r, e⟩': '(e,r)',
                       'texV2 ⟨n, d⟩': '(n-d,n+d)', 'texV2 ⟨r, e⟩': '(r-e,r+e)'}
            vlit = pair_s(v).replace(' ', '')
            single = expr.strip() in defform
            if (single and defform[expr.strip()] == vlit) or (expr.strip() == 'texV1Odd ⟨n, d⟩ + texV1Even ⟨r, e⟩' and vlit == '(2*d+e,2*n+r)'):
                body = f"(by unfold {' '.join(used)}; rfl)"
            elif single or '+' in expr:
                extra = ['Prod.mk_add_mk'] if '+' in expr else []
                body = f"(by unfold {' '.join(used)}; simp only [{', '.join(extra + ['Prod.mk.injEq'])}]; constructor <;> ring)"
            else:
                body = None
            out.append(f"  · exact mem_shift_piece _ _ _ _ {body} ({pn} n d e r hn hnd hr hre hdet hodd heven) z {h}")
    return out

HELPERS = """
theorem mem_zero_piece (C f : Fraction) (P : ∀ w : ℤ × ℤ, InH f w → InH C (((0 : ℤ), (0 : ℤ)) + w))
    (z : ℤ × ℤ) (hz : InH f z) : InH C z := by
  have h := P z hz
  rwa [show ((0 : ℤ), (0 : ℤ)) + z = z from by ext <;> simp] at h

theorem mem_shift_piece (C f : Fraction) (u v : ℤ × ℤ) (huv : u = v)
    (P : ∀ w : ℤ × ℤ, InH f w → InH C (v + w)) (z : ℤ × ℤ) (hz : z ∈ shiftS (HSet f) u) :
    InH C z := by
  obtain ⟨x, hx, hxz⟩ := hz
  have hxz' : x + u = z := hxz
  subst huv
  rw [← hxz', add_comm]
  exact P x hx
"""

if __name__ == "__main__":
    import os
    HERE = os.path.dirname(os.path.abspath(__file__))
    ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
    body = emit_grades_all()
    for m in (1, 2):
        for dl in (1, -1):
            body += emit_pieces(m, dl)
    fin = []
    for kind in ('even', 'odd'):
        for dl in (1, -1):
            fin += emit_final(kind, dl) + [""]
    hdr = """import FLatticePaper.Tiles.EncFam
import FLatticePaper.Tiles.SitePairScope

namespace FLatticePaper.Tiles.EncPieces

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Construction
open FLatticePaper.Tiles.EncUpper FLatticePaper.Tiles.EncFam FLatticePaper.Tiles.SitePairScope

"""
    wrappers = open(os.path.join(HERE, "pair_wrappers.lean.txt")).read()
    text = hdr + HELPERS + "\n" + "\n".join(body) + "\n" + "\n".join(fin) + "\n" + wrappers + "end FLatticePaper.Tiles.EncPieces\n"
    path = os.path.join(ROOT, "FLatticePaper", "Tiles", "EncPieces.lean")
    if len(sys.argv) > 1 and sys.argv[1] == "--stdout":
        print(text, end="")
    else:
        open(path, "w").write(text)
        print("wrote", path)
