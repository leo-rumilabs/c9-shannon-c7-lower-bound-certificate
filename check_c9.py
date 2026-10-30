#!/usr/bin/env python3
"""Exact checker for a new lower bound on C9 = Theta(C_7), the Shannon capacity of the 7-cycle.

Claim.  C_7^{box d} has an independent set of size M (both in certificate.json),
so Theta(C_7) >= M^(1/d), strictly above the previous record M_Tan^(1/500) =
3.25883262035... of [Tan2026] (arXiv:2608.30273, README value 3.25883262).

Construction (all ingredients are Tan's; only the way they are combined is new).
  * Tan's Theorem 1 (heterogeneous Gao product) builds HetGao(L, R)[J0, JH, JV]
    from gadgets L, R and codebooks J0, JH, JV living in L's space.  The
    codebook sizes and the counts q = |J \\ N(X_L^0)| depend on L only, never on
    R.  Tan's chain uses ten such left patterns (L, J0, JH, JV); their q values
    are the five certificates C1, C2, C3, C4, q15 (or trivial).  PATTERNS below
    lists them, copied from Tan's construction.py, and the checker asserts that
    they reproduce Tan's own gadgets.  The certificate applies these SAME
    patterns to other right factors R (base G5, or earlier outputs), which
    needs no new count.  One additional pattern 'Ppp' (L = G30^{++}) uses a
    NEW count q, computed live by this script with Tan's exact block counter
    (see gpp30_pattern); its block sets are checked against the profile.
  * v4: sibling patterns 'S<A,B,P>' generalise Ppp to L = Gao(A, B) for
    Tan's 5/10/15-dimensional gadgets: J0 = X(HetGao_P(A, B)) for a certified
    pattern P whose left factor is A (same ordered input pair), JH = JV = T(I)
    for a Gao main code I of matching shape, with q = |T(I) \\ N(X^0(Gao(A, B)))|
    counted live (see sibling_pattern).  All block sets are checked against
    profiles.
  * gao: Gao's product lemma (Tan's Lemma 1), valid for any two gadgets.
  * sigma (swap of the two transversal roles) and Phi (Gao profile -> BPZ
    seven-family vector, Tan eq. 77) as in Tan's code.
  * BPZ top level: one admissible combining rule and one terminal code
    (on k equal rule subtrees, or on k different ones via top['subtrees']),
    re-checked here (rule_problems == [], code_problems == []).

The checker uses integers only (no floats):
  1. derives C1..C4, q15 live from the 367-word base data and rebuilds Tan's
     Theorem 2 chain, checking it reproduces M_Tan at d = 500;
  2. evaluates the certificate's expression tree, tracking dimensions
     (Gao/HetGao and BPZ products add dimensions; G5 has dimension 5);
  3. checks (M, d) against the certificate;
  4. proves M^500 > M_Tan^d and M * 10^(8d) > 325883262^d;
  5. prints truncated digits of both roots (integer bisection).
Exit code 0 only if every check passes.

Usage:  python3 check_c9.py [certificate.json]      (Python >= 3.9, stdlib only)
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor_tan'))

from shannon import bpz  # noqa: E402
from shannon import construction as C  # noqa: E402
from shannon.gadget import (Phi, SideCodebook, gao, hetgao, neutral_from,  # noqa: E402
                            own_auxiliary, sigma)

PREV_NUM, PREV_DEN, PREV_TEXT = 325883262, 10 ** 8, '3.25883262'
# the d = 600 certificate of milestone/C9 (sha256 398de58f...), 3.258835653413235...
OURS_M, OURS_D = int('68782102619964681969555285794624154800149771897010939047546783272229624932740663217063197930989810561633354988997218956795087393101160960129102480293102611659504299642504317550407383021095331345453107345350494939327245702078716068519047974149335908885484759167694712839221151268207861515251467990973059034241'), 600


def fail(msg):
    print(f'FAIL: {msg}')
    sys.exit(1)


def tan_patterns(led, t2):
    """The certified left patterns of Tan's chain, with the dimension of L."""
    c = lambda k: C._cert(led, k)  # noqa: E731
    G10, G10A, G10D = t2['G10'], t2['G10A'], t2['G10D']
    Jplus, X10 = SideCodebook(G10.a, c('C1')), own_auxiliary(G10)
    G15X, G15h, G15AX, G15Ah, G15DX, G15Dh = (t2[k] for k in ('G15X', 'G15h', 'G15AX', 'G15Ah', 'G15DX', 'G15Dh'))
    J15, X15, X15X = SideCodebook(G15X.a, c('C2')), SideCodebook(G15h.s, c('C3')), own_auxiliary(G15X)
    J30pp, J15w = SideCodebook(t2['Gpp30'].a, c('C4')), SideCodebook(G15h.a, c('q15'))
    pats = {
        'P10': (G10, dict(J0=neutral_from(G10), JH=Jplus, JV=Jplus), 10),
        'P10A': (G10A, dict(J0=neutral_from(G10A), JH=Jplus, JV=X10), 10),
        'P10D': (G10D, dict(J0=neutral_from(G10D), JH=X10, JV=Jplus), 10),
        'P15X': (G15X, dict(J0=neutral_from(G15h), JH=J15, JV=J15), 15),
        'P15A8': (G15AX, dict(J0=neutral_from(G15Ah), JH=J15, JV=J15), 15),
        'P15Ah': (G15AX, dict(J0=neutral_from(G15Ah), JH=J15, JV=X15X), 15),
        'P15A5': (G15AX, dict(J0=neutral_from(G15Ah), JH=J15, JV=X15), 15),
        'P15D': (G15DX, dict(J0=neutral_from(G15Dh), JH=X15, JV=J15), 15),
        'P30L': (t2['G30L'], dict(J0=neutral_from(t2['Ghat30']), JH=J30pp, JV=J30pp), 30),
        'P15w': (G15h, dict(J0=neutral_from(G15h), JH=J15w, JV=J15w), 15),
    }
    # each pattern reproduces the gadget Tan builds with it
    G5, sG5 = C.base_profiles(led)
    same = lambda p, q: p.as_tuple() == q.as_tuple()  # noqa: E731
    checks = [
        same(hetgao(G10, G5, **pats['P10'][1]), G15h),
        same(hetgao(G10A, G5, **pats['P10A'][1]), G15Ah),
        same(hetgao(G10D, sG5, **pats['P10D'][1]), G15Dh),
        same(hetgao(G15X, G15h, **pats['P15X'][1]), t2['G30_6']),
        same(hetgao(G15AX, G10D, **pats['P15A8'][1]), t2['G25_8']),
        same(hetgao(G15AX, sigma(G15Ah), **pats['P15Ah'][1]), t2['Ghat30']),
        same(hetgao(G15AX, G10D, **pats['P15A5'][1]), t2['Ghat25']),
        same(hetgao(G15DX, t2['G25_8'], **pats['P15D'][1]), t2['G40_8']),
        same(hetgao(t2['G30L'], t2['G25R'], **pats['P30L'][1]), t2['G55']),
    ]
    if not all(checks):
        fail(f'a pattern does not reproduce Tan\'s gadget: {checks}')
    # P15w is the warm-up pattern of Tan's Section 3.1 (certificate q15)
    w = C.warmup(led)
    if not same(hetgao(G15h, G10, **pats['P15w'][1]), w['G25h']):
        fail('P15w does not reproduce Tan\'s G25^het')
    return pats


def gpp30_pattern(led, t2):
    """One NEW left pattern, counted live here with Tan's exact block counter.

    L = G30^{++} = Gao(G15^het, G15^het).  J0 = X(G30^het) of Tan's Section 3.1,
    built from the same ordered input pair (G15^het, G15^het), hence legitimate
    as a neutral codebook for L (Tan, construction of neutral_from).  JH = JV =
    T(I_30^{++}), the automorphic image Tan already uses as J_30^{++} (an
    independent set), with the new count q = |T(I_30^{++}) minus N(X^0(G30^{++}))|,
    where X^0 of a Gao product is X_L^0 x X_R^0 u (X_L^H u X_L^V) x (X_R^H u X_R^V)
    (Tan's Lemma 1: o = o1 o2 + (h1 + v1)(h2 + v2)).
    """
    from shannon import certificates as CT
    base, T, exchanges, _ = CT.load_base()
    G, _, _ = CT.build(base, T, exchanges, verbose=False)
    HV = G['X15_H'] + G['X15_V']
    ref = CT.cross(G['X15_0'], G['X15_0']) + CT.cross(HV, HV)
    I30pp = [b for _, bl in CT.components(G) for b in bl]
    Gpp = t2['Gpp30']
    if CT.size(ref) != Gpp.o or CT.size(I30pp) != Gpp.a:
        fail('block sets do not match the profile of G30^{++}')
    q = CT.count_outside(CT.apply_T_blocks(I30pp, T), ref)
    print(f'  new count q = |T(I_30^++) \\ N(X^0(G30^++))| = {q}  (j = {Gpp.a}; |X^0| = {Gpp.o} checked)')
    w = C.warmup(led)
    if w['G30h'].as_tuple()[:2] != Gpp.as_tuple()[:2]:
        fail('G30^het and G30^{++} must share code and private pairs')
    J = SideCodebook(Gpp.a, q)
    return (Gpp, dict(J0=neutral_from(w['G30h']), JH=J, JV=J), 30)


def sibling_pattern(led, t2, pats, A_name, B_name, P_name):
    """NEW left pattern S<A,B,P>, counted live with Tan's exact block counter.

    L = Gao(A, B), where A is the left factor of a certified pattern P (one of
    Tan's 10- or 15-dimensional gadgets) and B is G5, one of Tan's 10- or
    15-dimensional gadgets, or a sigma image (prefix 's').  X^0 of a Gao
    product depends only on the physical sets X_A^0, X_A^H u X_A^V, X_B^0,
    X_B^H u X_B^V (Tan's Lemma 1: o = o1 o2 + (h1 + v1)(h2 + v2)), and sigma
    only swaps the H and V roles.  The physical block sets are Tan's (base
    X^0 / X^H u X^V; X_10^0 / X_10^r shared by G10, G10^A, G10^D; X_15^{0,X} /
    X_15^{r,X} shared by G15^X, G15^{A,X}, G15^{D,X}; X_15^0 / X_15^H u X_15^V;
    X_15^{A,0} / X_15^{A,r} for G15^{A,het} and G15^{D,het} = sigma
    G15^{A,het}).  Their sizes are checked against o and h + v of each profile.
    J0 = X(HetGao_P(A, B)), the auxiliary set that Tan's Theorem 1 builds from
    the same ordered input pair (A, B), exactly as Ppp uses X(G30^het) and P30L
    uses X(Ghat30).  JH = JV = T(I), where I is the main code of Gao(S_A, S_B)
    with S = G5, G10 or G15^het of the same dimensions as A, B.  I is built
    from Tan's main-code blocks with Tan's own product formula (asserted to
    reproduce Tan's I_15 and I_30^{++} block for block) and its size is checked
    against a(Gao(S_A, S_B)).  It is an independent set; j = |I| need not equal
    a(L), as with J_30^{++} in P30L.
    """
    from shannon import certificates as CT
    base, T, exchanges, _ = CT.load_base()
    G, _, _ = CT.build(base, T, exchanges, verbose=False)
    g = base
    At = {a.name: a for key in G for blk in G[key] for a in blk}
    one = lambda *atoms: [(x,) for x in atoms]  # noqa: E731
    G5, sG5 = C.base_profiles(led)
    prof = {'G5': G5, 'sG5': sG5}
    phys = {'G5': '5', 'G10': '10', 'G10A': '10', 'G10D': '10', 'G15X': 'X', 'G15AX': 'X', 'G15DX': 'X',
            'G15h': 'h', 'G15Ah': 'A', 'G15Dh': 'A'}
    aux = {'5': (one(g.X0), one(g.XH, g.XV)), '10': (one(At['X2_0']), one(At['X2_r'])),
           'X': (G['X15X_0'], G['X15X_r']), 'h': (G['X15_0'], G['X15_H'] + G['X15_V']),
           'A': (G['X15A_0'], G['X15A_r'])}
    dim = {'5': 5, '10': 10, 'X': 15, 'h': 15, 'A': 15}
    # main-code block sets (B = I minus R, R, P^H, P^V) and auxiliary classes of G5, G10, G15^het
    main = {5: (dict(B=one(g.B), R=one(g.R), PH=one(g.PH), PV=one(g.PV), X0=one(g.X0), XH=one(g.XH), XV=one(g.XV)), G5),
            10: (dict(B=one(At['B2']), R=one(At['R2']), PH=one(At['PH2']), PV=one(At['PV2']),
                      X0=one(At['X2_0']), XH=one(At['X2_H']), XV=one(At['X2_V'])), t2['G10']),
            15: (dict(B=G['B15'], R=G['R15'], PH=G['PH15'], PV=G['PV15'], X0=G['X15_0'], XH=G['X15_H'], XV=G['X15_V']),
                 t2['G15h'])}
    def main_code(Ls, Rs):
        c = CT.cross
        return (c(Ls['B'], Rs['B']) + c(Ls['R'], Rs['X0']) + c(Ls['PH'], Rs['XH']) + c(Ls['PV'], Rs['XV'])
                + c(Ls['X0'], Rs['R']) + c(Ls['XH'], Rs['PV']) + c(Ls['XV'], Rs['PH']))
    key = lambda bl: sorted(tuple(id(x) for x in b) for b in bl)  # noqa: E731
    I15 = [(At['B2'], g.B), (At['R2'], g.X0), (At['PH2'], g.XH), (At['PV2'], g.XV),
           (At['X2_0'], g.R), (At['X2_H'], g.PV), (At['X2_V'], g.PH)]
    if key(main_code(main[10][0], main[5][0])) != key(I15) or \
            key(main_code(main[15][0], main[15][0])) != key([b for _, bl in CT.components(G) for b in bl]):
        fail('product formula does not reproduce Tan\'s I_15 / I_30^{++}')
    def gadget(nm):
        sg = nm.startswith('s') and nm[1:] in phys
        k = nm[1:] if sg else nm
        if k not in phys:
            fail(f'unknown gadget {nm}')
        p = prof[k] if k in prof else t2[k]
        p = sigma(p) if sg else p
        X0, Xr = aux[phys[k]]
        if CT.size(X0) != p.o or CT.size(Xr) != p.h + p.v:
            fail(f'block sets do not match the profile of {nm}')
        return p, X0, Xr, dim[phys[k]]
    A, XA0, XAr, dA = gadget(A_name)
    B, XB0, XBr, dB = gadget(B_name)
    L = gao(A, B)
    ref = CT.cross(XA0, XB0) + CT.cross(XAr, XBr)
    (SA, PA), (SB, PB) = main[dA], main[dB]
    I = main_code(SA, SB)
    if CT.size(ref) != L.o or CT.size(I) != gao(PA, PB).a:
        fail('block sets do not match the profiles of Gao(A, B) and of the main-code product')
    left = {'P10': 'G10', 'P10A': 'G10A', 'P10D': 'G10D', 'P15X': 'G15X', 'P15A8': 'G15AX', 'P15Ah': 'G15AX',
            'P15A5': 'G15AX', 'P15D': 'G15DX', 'P15w': 'G15h'}
    if left.get(P_name) != A_name:
        fail(f'pattern {P_name} does not have left factor {A_name}')
    PL, kw, dl = pats[P_name]
    if dl != dA or PL.as_tuple() != A.as_tuple():
        fail(f'pattern {P_name} does not have left factor {A_name}')
    Lhet = hetgao(PL, B, **kw)
    if Lhet.as_tuple()[:2] != L.as_tuple()[:2]:
        fail('HetGao_P(A, B) and Gao(A, B) must share code and private pairs')
    q = CT.count_outside(CT.apply_T_blocks(I, T), ref)
    j = CT.size(I)
    print(f'  new count q = |T(I_{dA + dB}) \\ N(X^0(Gao({A_name},{B_name})))| = {q}  (j = |I| = {j}; |X^0| = {L.o} checked)')
    J = SideCodebook(j, q)
    S1 = gao_sets(SA, SB)
    XLr = CT.cross(XAr, XB0) + CT.cross(XA0, XBr)
    if key(S1['B'] + S1['R']) != key(I) or CT.size(XLr) != L.h + L.v:
        fail('gao_sets / X^H u X^V of Gao(A, B) do not match')
    _CHAIN[f'S<{A_name},{B_name},{P_name}>'] = (S1, (ref, XLr), gao(PA, PB), gadget, main, T)
    return (L, dict(J0=neutral_from(Lhet), JH=J, JV=J), dA + dB)


def gao_sets(L, R):
    """main-code split (B = I minus R, R, P^H, P^V) and auxiliary classes of Gao(L, R), from those of L and R
    (Tan's product formula, the same one main_code uses for B + R)"""
    c = CT_cross()
    return dict(B=c(L['B'], R['B']) + c(L['PH'], R['XH']) + c(L['PV'], R['XV']) + c(L['XH'], R['PV'])
                + c(L['XV'], R['PH']),
                R=c(L['R'], R['X0']) + c(L['X0'], R['R']),
                PH=c(L['PH'], R['X0']) + c(L['X0'], R['PV']), PV=c(L['PV'], R['X0']) + c(L['X0'], R['PH']),
                X0=c(L['X0'], R['X0']) + c(L['XH'] + L['XV'], R['XH'] + R['XV']),
                XH=c(L['XH'], R['X0']) + c(L['X0'], R['XV']), XV=c(L['XV'], R['X0']) + c(L['X0'], R['XH']))


def CT_cross():
    from shannon import certificates as CT
    return CT.cross


_CHAIN = {}


def chain_pattern(led, t2, pats, name):
    """NEW nested left pattern N<Q,C> for a sibling or nested pattern Q (any depth): L2 = Gao(L1, C), where L1 is
    the left gadget of Q and C is G5, a 10/15-dim Tan gadget or a sigma image.  By Tan's Lemma 1,
    X^0(L2) = X^0(L1) x X_C^0 u X^r(L1) x X_C^r and X^r(L2) = X^r(L1) x X_C^0 u X^0(L1) x X_C^r (X^r = X^H u X^V);
    their sizes are checked against o(L2) and h + v of L2 at every level.  J0 = X(HetGao_Q(L1, C)), the auxiliary
    set of Tan's Theorem 1 for the same ordered input pair (L1, C); it must share (a, t) with Gao(L1, C).
    JH = JV = T(I), I the main code of Gao(M_Q, S_C), where M_Q is the main-code product of Q and S_C = G5, G10
    or G15^het, built with the product formula (size checked against a of the profile product)."""
    from shannon import certificates as CT
    if name in pats and name in _CHAIN:
        return pats[name]
    if name.startswith('S<'):
        a, b, p = name[2:-1].split(',')
        pats[name] = sibling_pattern(led, t2, dict(pats), a, b, p)
        return pats[name]
    if not name.startswith('N<') or '>,' not in name:
        fail(f'unknown pattern {name}')
    inner, c_name = name[2:-1].rsplit('>,', 1)
    inner += '>'
    PL1, kw1, dl1 = chain_pattern(led, t2, pats, inner)
    sets, (X0, Xr), PM, gadget, main, T = _CHAIN[inner]
    C_, XC0, XCr, dC = gadget(c_name)
    L2 = gao(PL1, C_)
    aux = (CT.cross(X0, XC0) + CT.cross(Xr, XCr), CT.cross(Xr, XC0) + CT.cross(X0, XCr))
    SC, PC = main[dC]
    sets2 = gao_sets(sets, SC)
    PM2 = gao(PM, PC)
    I = sets2['B'] + sets2['R']
    if CT.size(aux[0]) != L2.o or CT.size(aux[1]) != L2.h + L2.v or CT.size(I) != PM2.a:
        fail(f'block sets do not match the profiles of the left gadget and the main-code product of {name}')
    Lhet = hetgao(PL1, C_, **kw1)
    if Lhet.as_tuple()[:2] != L2.as_tuple()[:2]:
        fail('HetGao_Q(L1, C) and Gao(L1, C) must share code and private pairs')
    q = CT.count_outside(CT.apply_T_blocks(I, T), aux[0])
    j = CT.size(I)
    print(f'  new count q = |T(I_{dl1 + dC}) \\ N(X^0(Gao(L({inner}),{c_name})))| = {q}  (j = |I| = {j}; |X^0| = {L2.o} checked)')
    J = SideCodebook(j, q)
    pats[name] = (L2, dict(J0=neutral_from(Lhet), JH=J, JV=J), dl1 + dC)
    _CHAIN[name] = (sets2, aux, PM2, gadget, main, T)
    return pats[name]


def main():
    cert_path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'certificate.json'
    raw = cert_path.read_bytes()
    cert = json.loads(raw)
    print(f'certificate {cert_path.name} sha256 {hashlib.sha256(raw).hexdigest()}')

    led = C.load_certificates(recomputed=True)   # raises if a live count differs from the ledger
    for name, entry in led['certificates'].items():
        print(f'  derived {name:<4} = {entry["value"]}')
    t2 = C.theorem2(led)
    if t2['M'] != bpz.apply_code(bpz.K4a, [bpz.apply_rule(bpz.S3b, [t2['n6'], t2['n11'], t2['n8']])] * 4):
        fail('Tan chain does not reproduce M_Tan')
    M_tan, d_tan = t2['M'], 500
    pats = tan_patterns(led, t2)
    print(f'  {len(pats)} certified HetGao left patterns reproduce Tan\'s gadgets')
    if any(st.get('pattern') == 'Ppp' for st in cert['gadgets']):
        pats['Ppp'] = gpp30_pattern(led, t2)
    for st in cert['gadgets']:
        if st.get('pattern', '')[:2] in ('S<', 'N<') and st['pattern'] not in pats:
            chain_pattern(led, t2, pats, st['pattern'])

    G5, sG5 = C.base_profiles(led)
    prof = {'G5': (G5, 5), 'sG5': (sG5, 5)}
    for st in cert['gadgets']:
        if st['name'] in prof:
            fail(f'duplicate name {st["name"]}')
        if st['op'] == 'hetgao':
            L, kw, dL = pats[st['pattern']]
            R, dR = prof[st['R']]
            prof[st['name']] = (hetgao(L, R, **kw), dL + dR)
        elif st['op'] == 'gao':
            (L, dL), (R, dR) = prof[st['L']], prof[st['R']]
            prof[st['name']] = (gao(L, R), dL + dR)
        elif st['op'] == 'sigma':
            p, d = prof[st['of']]
            prof[st['name']] = (sigma(p), d)
        else:
            fail(f'unknown op {st["op"]}')
        print(f'  {st["name"]:<6} dim {prof[st["name"]][1]:>3}  {st}')
    vec = {'n6': (t2['n6'], 30), 'n11': (t2['n11'], 55), 'n8': (t2['n8'], 40)}
    for k, (p, d) in prof.items():
        vec['Phi(' + k + ')'] = (Phi(p), d)
    top = cert['top']
    rule, code = bpz.RULES[top['rule']], bpz.CODES[top['terminal_code']]
    if bpz.rule_problems(rule) or bpz.code_problems(code):
        fail('rule not admissible or terminal code not separated')
    k = len(code[0])
    # 'rule_inputs': one rule subtree, k equal copies; 'subtrees': k (possibly different) rule subtrees.
    # A terminal word (l_1..l_k) contributes prod_i |X_{l_i}(n_i)|; two words are separated in some
    # coordinate i by a perp pair of labels, i.e. inside the single gadget n_i, so the copies need not be equal.
    subs = top['subtrees'] if 'subtrees' in top else [top['rule_inputs']] * k
    if len(subs) != k:
        fail('number of subtrees != terminal code arity')
    ns, d = [], 0
    for sub in subs:
        ins = [vec[x] for x in sub]
        if any(min(v) < 0 for v, _ in ins):
            fail('negative family size')
        ns.append(bpz.apply_rule(rule, [v for v, _ in ins]))
        d += sum(dd for _, dd in ins)
        print(f'  subtree {top["rule"]}{tuple(sub)}, dim {sum(dd for _, dd in ins)}')
    M = bpz.apply_code(code, ns)
    print(f'  top = {top["terminal_code"]} on {k} subtrees')
    print(f'  M: {len(str(M))} digits, dimension d = {d}')
    if d != cert['dimension'] or M != int(cert['M']):
        fail('recomputed (M, d) differs from the certificate')

    if not M ** d_tan > M_tan ** d:
        fail('M^(1/d) does not exceed M_Tan^(1/500)')
    if not M * PREV_DEN ** d > PREV_NUM ** d:
        fail(f'M^(1/d) does not exceed {PREV_TEXT}')
    if not M ** OURS_D > OURS_M ** d:
        fail('M^(1/d) does not exceed the d = 600 certificate')
    print(f'  strictly above the d = {OURS_D} certificate {C.nth_root_digits(OURS_M, OURS_D, 15)}... (exact: M^{OURS_D} > M_600^{d})')
    new, old = C.nth_root_digits(M, d, 15), C.nth_root_digits(M_tan, d_tan, 15)
    print(f'CERTIFIED  Theta(C_7) >= M^(1/{d}) >= {new}   (exact: M^500 > M_Tan^{d} and M*10^(8*{d}) > {PREV_NUM}^{d})')
    print(f'PREVIOUS   Theta(C_7) >= M_Tan^(1/500) = {old}...   [Tan2026], README value {PREV_TEXT}')
    print('OK')
    return 0


if __name__ == '__main__':
    sys.exit(main())
