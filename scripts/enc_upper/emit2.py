from gen_fam import L, site_ops, MIN
from gen_fam2 import sym_parts, margin_sym, qr

def zpar(VT, w='w'):
    return f"decide ((({VT} + {w}).1 + ({VT} + {w}).2) % 2 = 0)"

def hX_stmt(m, delta, f, facet, Dn, K, C, F):
    if f == 'P':
        if facet == 't':
            tail = "+ sCo F w" if delta == 1 else "- sCo F w"
            s = f"{Dn} * tCo C w = ({m} * {Dn} + {K}) * tCo F w {tail}"
        else:
            tail = "+ 2 * tCo F w" if delta == 1 else "- 2 * tCo F w"
            s = f"{Dn} * sCo C w = ({m} * {Dn} + {K}) * sCo F w {tail}"
    else:
        if facet == 't':
            tail = f"- {m} * sCo F w" if delta == 1 else f"+ {m} * sCo F w"
            s = f"{Dn} * tCo C w = ({Dn} + {m} * {K}) * tCo F w {tail}"
        else:
            tail = f"- 2 * {m} * tCo F w" if delta == 1 else f"+ 2 * {m} * tCo F w"
            s = f"{Dn} * sCo C w = ({Dn} + {m} * {K}) * sCo F w {tail}"
    return s.replace("tCo C", f"tCo {C}").replace("sCo C", f"sCo {C}").replace("tCo F", f"tCo {F}").replace("sCo F", f"sCo {F}")

R_HINTS = ("[hnd, hr, _hre, _hn, hb1, hb2, "
           "mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), "
           "mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), "
           "mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), " "mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), "
           "mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), "
           "mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), " "mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), "
           "mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), "
           "mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), "
           "mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), "
           "mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), "
           "mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), "
           "mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]")

def sigs(m, delta, f):
    op, oq = site_ops(m, delta)
    orig = op if f == 'P' else oq
    vt = orig[MIN[(m, delta, f, 't')]]; vs = orig[MIN[(m, delta, f, 's')]]
    VT = f"({L(vt[0])}, {L(vt[1])})"; VS = f"({L(vs[0])}, {L(vs[1])})"
    pn, pd = ('n', 'd') if f == 'P' else ('r', 'e')
    C = f"⟨{m} * n + r, {m} * d + e⟩"; F = f"⟨{pn}, {pd}⟩"
    Dn = '(d ^ 2 + 2 * d * n - n ^ 2)' if f == 'P' else '(e ^ 2 + 2 * e * r - r ^ 2)'
    K = '((d + n) * e + (d - n) * r)'
    TC = f"(({m} * d + e) ^ 2 + 2 * ({m} * d + e) * ({m} * n + r) - ({m} * n + r) ^ 2)"
    return dict(VT=VT, VS=VS, pn=pn, pd=pd, C=C, F=F, Dn=Dn, K=K, TC=TC, vt=vt, vs=vs)

def conc(S):
    C, VT, VS = S['C'], S['VT'], S['VS']
    return (f"aOf {C} (decide ((w.1 + w.2) % 2 = 0)) - tOf {C} ≤ tCo {C} ({VT} + w) ∧\n"
            f"      lOf {C} (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo {C} ({VS} + w)")

HDR = ("(n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)\n"
       "    (hdet : d * r - n * e = {DL}) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)\n"
       "    (w : ℤ × ℤ) (hw : InH {F} w)")

def emit_branch(m, delta, f, parity, branch):
    S = sigs(m, delta, f)
    DL = f"{delta}" if delta == 1 else "-1"
    DLp = f"({DL})"
    sfx = ('p' if delta == 1 else 'n')
    name = f"fam_{f}{m}{sfx}_{'e' if parity=='even' else 'o'}_{'b' if branch=='below' else 'a'}"
    C, F, Dn, K, TC, VT, VS = S['C'], S['F'], S['Dn'], S['K'], S['TC'], S['VT'], S['VS']
    pn, pd = S['pn'], S['pd']
    dl_hyp = "hpar : (w.1 + w.2) % 2 = 0" if parity == 'even' else "hpar : ¬ (w.1 + w.2) % 2 = 0"
    if parity == 'even':
        br_hyp = ("hb : 3 * n ≤ d ∧ 3 * r ≤ e" if branch == 'below' else "hb : d ≤ 3 * n ∧ e ≤ 3 * r")
    else:
        br_hyp = ("hb : 2 * n ≤ d ∧ 2 * r ≤ e" if branch == 'below' else "hb : d ≤ 2 * n ∧ e ≤ 2 * r")
    so = "Or.inl rfl" if delta == 1 else "Or.inr rfl"
    cm = "Or.inl rfl" if m == 1 else "Or.inr rfl"
    out = []; A = out.append
    A(f"theorem {name} " + HDR.replace("{DL}", DLp).replace("{F}", F) + f"\n    ({dl_hyp}) ({br_hyp}) :")
    A("    " + conc(S) + " := by")
    A(f"  have hb1 := hb.1")
    A(f"  have hb2 := hb.2")
    A(f"  obtain ⟨hr1, he1⟩ := re_odd n d r e {DLp} hdet ({so}) heven")
    if f == 'P':
        A(f"  have hD : 0 < {Dn} := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]")
    else:
        A(f"  have hD : 0 < {Dn} := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]")
    A(f"  have hK : 0 ≤ {K} := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]")
    A(f"  have hdzT : decide ((({VT} + w).1 + ({VT} + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=")
    A(f"    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)")
    A(f"  have hdzS : decide ((({VS} + w).1 + ({VS} + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=")
    A(f"    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)")
    A(f"  have hTC : tOf {C} = {TC} := by unfold tOf; ring")
    if m == 2:
        A(f"  have hnumC : (2 * n + r) % 2 = 1 := by omega")
        A(f"  have hdenC : (2 * d + e) % 2 = 1 := by omega")
    else:
        A(f"  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega")
    ident = {('P','t'): 'ident_tP', ('P','s'): 'ident_sP', ('Q','t'): 'ident_tQ', ('Q','s'): 'ident_sQ'}
    for facet in ('t', 's'):
        A(f"  have hX{facet} : {hX_stmt(m, delta, f, facet, Dn, K, C, F)} := by")
        A(f"    have h := {ident[(f, facet)]} n d e r {m} w; rw [hdet] at h; linarith only [h]")
    if parity == 'even':
        A(f"  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := {F}) hpar).mp hw")
    else:
        A(f"  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := {F}) hpar).mp hw")
    A(f"  dsimp only at hA1 hA2 hA3 hA4")
    sp_ = sym_parts(m, delta, f, parity, branch)
    aF_s = sp_['aF'][1]; lF_s = sp_['lF'][1]; aC_s = sp_['aC'][1]; lC_s = sp_['lC'][1]
    g0t_s = sp_['g0t_s']; g0s_s = sp_['g0s_s']
    Lf = '(d + n)' if f == 'P' else '(e + r)'
    if parity == 'even':
        if branch == 'below':
            A(f"  have hPa : aOf {F} true = {aF_s} := aOf_mk_true_le {pn} {pd} (by omega)")
        else:
            A(f"  have hPa : aOf {F} true = {aF_s} := aOf_mk_true_ge {pn} {pd} (by omega)")
        A(f"  have hPl : lOf {F} true = 0 := lOf_mk_true {pn} {pd}")
        cA = f"childA_true_below n d r e {m} ({cm}) hb" if branch == 'below' else f"childA_true_above n d r e {m} ({cm}) hb"
        A(f"  have hCa : aOf {C} true = {aC_s} := {cA}")
        A(f"  have hCl : lOf {C} true = 0 := lOf_true' {C}")
        dec = "decide_eq_true hpar"
    else:
        A(f"  have hPa : aOf {F} false = {aF_s} := aOf_mk_false {pn} {pd}")
        if branch == 'below':
            A(f"  have hPl : lOf {F} false = {lF_s} := lOf_mk_false_le {pn} {pd} (by omega)")
            cL = f"childL_false_below n d r e {m} ({cm}) hb"
        else:
            A(f"  have hPl : lOf {F} false = {lF_s} := lOf_mk_false_ge {pn} {pd} (by omega)")
            cL = f"childL_false_above n d r e {m} ({cm}) hb"
        A(f"  have hCa : aOf {C} false = {aC_s} := aOf_child_false {m} n r d e")
        A(f"  have hCl : lOf {C} false = {lC_s} := {cL}")
        dec = "decide_eq_false hpar"
    if f == 'P':
        A(f"  have hPm : muOf {F} = 2 := muOf_mk_two n d (by omega)")
    else:
        A(f"  have hPm : muOf {F} = 1 := muOf_mk_one r e (by omega)")
    A(f"  have hPt : tOf {F} = {Dn} := tOf_mk {pn} {pd}")
    A(f"  rw [hPm, hPt, hPl] at hA4")
    mu = 2 if f == 'P' else 1
    A(f"  have bTlo : {aF_s} - {Dn} ≤ tCo {F} w := by linarith only [hA1, hPa, hPt]")
    A(f"  have bThi : tCo {F} w ≤ {Lf} - {aF_s} := by linarith only [hA2, hPa]")
    A(f"  have bSlo : {lF_s} ≤ sCo {F} w := by linarith only [hA3, hPl]")
    A(f"  have bShi : sCo {F} w ≤ {mu} * {Dn} + 2 * {pn} - {lF_s} := by linarith only [hA4]")
    for facet in ('t', 's'):
        Mx, k = margin_sym(m, delta, f, facet, sp_)
        q, R = qr(Mx, delta)
        A(f"  have hq{facet} : (d * r - n * e - ({DLp})) * ({L(q)}) = 0 := by")
        A(f"    rw [show d * r - n * e - ({DLp}) = 0 by linarith only [hdet], zero_mul]")
        A(f"  have hR{facet} : 0 < {L(R)} := by nlinarith only {R_HINTS}")
        hM = f"(by linarith only [hq{facet}, hR{facet}])"
        if f == 'P' and facet == 't':
            if delta == 1:
                call = f"base_tP_pos (X := tCo {C} w) (tP := tCo {F} w) (sP := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (aP := {aF_s}) (lP := {lF_s}) (aC := ({aC_s})) (TC := {TC}) (g0 := {g0t_s}) (k := {k}) hD hK (by norm_num) hXt bTlo bSlo {hM}"
            else:
                call = f"base_tP_neg (X := tCo {C} w) (tP := tCo {F} w) (sP := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (aP := {aF_s}) (hi := ({mu} * {Dn} + 2 * {pn} - {lF_s})) (aC := ({aC_s})) (TC := {TC}) (g0 := {g0t_s}) (k := {k}) hD hK (by norm_num) hXt bTlo bShi {hM}"
        elif f == 'P' and facet == 's':
            if delta == 1:
                call = f"base_sP_pos (X := sCo {C} w) (tP := tCo {F} w) (sP := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (lP := {lF_s}) (aP := {aF_s}) (lC := ({lC_s})) (g0 := {g0s_s}) (k := {k}) hD hK (by norm_num) hXs bTlo bSlo {hM}"
            else:
                call = f"base_sP_neg (X := sCo {C} w) (tP := tCo {F} w) (sP := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (lP := {lF_s}) (hi := ({Lf} - {aF_s})) (lC := ({lC_s})) (g0 := {g0s_s}) (k := {k}) hD hK (by norm_num) hXs bThi bSlo {hM}"
        elif f == 'Q' and facet == 't':
            if delta == 1:
                call = f"base_tQ_pos (X := tCo {C} w) (tQ := tCo {F} w) (sQ := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (aQ := {aF_s}) (hi := ({mu} * {Dn} + 2 * {pn} - {lF_s})) (aC := ({aC_s})) (TC := {TC}) (g0 := {g0t_s}) (k := {k}) hD hK (by norm_num) hXt bTlo bShi {hM}"
            else:
                call = f"base_tQ_neg (X := tCo {C} w) (tQ := tCo {F} w) (sQ := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (aQ := {aF_s}) (lQ := {lF_s}) (aC := ({aC_s})) (TC := {TC}) (g0 := {g0t_s}) (k := {k}) hD hK (by norm_num) hXt bTlo bSlo {hM}"
        else:
            if delta == 1:
                call = f"base_sQ_pos (X := sCo {C} w) (tQ := tCo {F} w) (sQ := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (lQ := {lF_s}) (hi := ({Lf} - {aF_s})) (lC := ({lC_s})) (g0 := {g0s_s}) (k := {k}) hD hK (by norm_num) hXs bThi bSlo {hM}"
            else:
                call = f"base_sQ_neg (X := sCo {C} w) (tQ := tCo {F} w) (sQ := sCo {F} w) (Dn := {Dn}) (K := {K}) (m := {m}) (lQ := {lF_s}) (aQ := {aF_s}) (lC := ({lC_s})) (g0 := {g0s_s}) (k := {k}) hD hK (by norm_num) hXs bTlo bSlo {hM}"
        A(f"  have b{facet} := {call}")
        if facet == 't':
            z = f"({VT} + w)"
            A(f"  have hz{facet} : tCo {C} {z} = ({g0t_s}) + tCo {C} w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring")
            A(f"  have hY{facet} : -{k} < tCo {C} {z} - ({aC_s}) + tOf {C} := by linarith only [bt, hzt, hTC]")
            A(f"  have hAz{facet} : aOf {C} ({zpar(VT)}) = {aC_s} := by rw [hdzT, {dec}, hCa]")
            if k == 1:
                A(f"  have c{facet} := lowT1 {C} {z} ({aC_s}) hAz{facet} hY{facet}")
            else:
                A(f"  have hp{facet} : (tCo {C} {z} - ({aC_s}) + tOf {C}) % 2 = 0 := by")
                A(f"    have := par_tA {C} hnumC hdenC {z}; rw [hAz{facet}] at this; exact this" if m == 2 else "    sorry")
                A(f"  have c{facet} := lowT2 {C} {z} ({aC_s}) hAz{facet} hp{facet} hY{facet}")
            A(f"  rw [hdzT] at c{facet}")
        else:
            z = f"({VS} + w)"
            A(f"  have hz{facet} : sCo {C} {z} = ({g0s_s}) + sCo {C} w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring")
            A(f"  have hY{facet} : -{k} < sCo {C} {z} - ({lC_s}) := by linarith only [bs, hzs]")
            A(f"  have hLz{facet} : lOf {C} ({zpar(VS)}) = {lC_s} := by rw [hdzS, {dec}, hCl]")
            if m == 2:
                A(f"  have hp{facet} : (sCo {C} {z} - ({lC_s})) % 2 = 0 := by")
                A(f"    have := par_sA {C} hnumC hdenC {z}; rw [hLz{facet}] at this; exact this")
            else:
                A(f"  have hp{facet} : (sCo {C} {z} - ({lC_s})) % 2 = 0 := by")
                A(f"    have := par_sB {C} hsumC {z}; rw [hLz{facet}] at this; exact this")
            A(f"  have c{facet} := lowS2 {C} {z} ({lC_s}) hLz{facet} hp{facet} hY{facet}")
            A(f"  rw [hdzS] at c{facet}")
    A(f"  exact ⟨ct, cs⟩")
    return out, name

def emit_top(m, delta, f):
    S = sigs(m, delta, f)
    DLp = f"({delta})" if delta == 1 else "(-1)"
    sfx = ('p' if delta == 1 else 'n')
    name = f"fam_{f}{m}{sfx}"
    C, F = S['C'], S['F']
    so = "Or.inl rfl" if delta == 1 else "Or.inr rfl"
    out = []; A = out.append
    A(f"theorem {name} " + HDR.replace("{DL}", DLp).replace("{F}", F) + " :")
    A("    " + conc(S) + " := by")
    A(f"  by_cases hpar : (w.1 + w.2) % 2 = 0")
    A(f"  · rcases side3 n d r e {DLp} _hn hnd hr _hre hdet ({so}) with hb | hb")
    A(f"    · exact {name}_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb")
    A(f"    · exact {name}_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb")
    A(f"  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar")
    A(f"    rcases side2 n d r e {DLp} _hn hnd hr _hre hdet ({so}) with hb | hb")
    A(f"    · exact {name}_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb")
    A(f"    · exact {name}_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb")
    return out, name

if __name__ == "__main__":
    o, nm = emit_branch(2, 1, 'P', 'even', 'below')
    print("\n".join(o))
