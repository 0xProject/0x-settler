#!/usr/bin/env python3
"""Emit FloorCertLit.lean: literal coefficient lists for the four main
certificate polynomials, mirroring the constructions in FloorCertDefs.lean."""
import math, sys
sys.set_int_max_str_digits(2000000)
sys.path.insert(0, "/home/user/Documents/git-repos/0x-settler-lnwad")
from formal.python.ln.check_ln_counterexample import (
    _S, _P4, _P3, _P2, _P1, _C0, _Q4, _Q3, _Q2, _Q1)

S = _S
K = 22
KF = math.factorial(K); KF1 = math.factorial(K + 1)
EUN, EUD = 36, 10**29

PPc = [_C0 * 2**358, -_P1 * 2**263, _P2 * 2**174, -_P3 * 2**84, _P4]
QQc = [-_C0 * 2**386, _Q1 * 2**291, -_Q2 * 2**203, _Q3 * 2**105, -_Q4, 1]
SLOPPc = 997337740623226022763231126257526602143516768691287840071060348738876110879097835502646319520435285356766016
SLOPQc = 237328394272566608543184577042992631102137769183554805465838453830626805665679633215510949390003272039043519320424448

def pmul(a, b):
    if not a or not b: return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out
def padd(a, b):
    out = list(a) if len(a) >= len(b) else list(b)
    for i, y in enumerate(b if len(a) >= len(b) else a):
        out[i] += y
    return out
def pscale(c, a): return [c * x for x in a]
def ppow(a, n):
    # mirror Lean polyPow: P^(n+1) = polyMul P (polyPow P n)
    r = [1]
    for _ in range(n): r = pmul(a, r)
    return r
def pneg(a): return [-c for c in a]

def hom(coeffs, num, den):
    # mirror Lean homPoly: Horner form with [0] base; keeps trailing zeros
    out = [0]
    for j in range(len(coeffs) - 1, -1, -1):
        out = padd(pscale(coeffs[j], ppow(den, len(coeffs) - 1 - j)), pmul(num, out))
    return out

def exp_poly_num(tn, td, k):
    # mirror Lean expPolyNum
    if k == 0: return [1]
    r = exp_poly_num(tn, td, k - 1)
    return padd(pscale(k, pmul(td, r)), ppow(tn, k))

def build_branch(sign):
    A = [-S, 1] if sign > 0 else [S, -1]
    B = [S, 1]
    A2 = pmul(A, A); B2 = pmul(B, B)
    WLO = padd(padd(pscale(2**99, A2), pneg(pmul(A, B))), pscale(-8, B2))
    D8 = pscale(8, B2)
    A96 = pscale(2**96, A2)
    PPHwlo = hom(PPc, WLO, D8)
    QQHws = hom(QQc, A96, B2)
    QQHwlo = hom(QQc, WLO, D8)
    PPHws = hom(PPc, A96, B2)
    TN = pscale(2**17, pmul(pmul(A, B), PPHwlo))
    TD = pneg(QQHws)
    PLOP = padd(PPHws, pscale(-SLOPPc, ppow(B2, 4)))
    DLO = padd(pneg(QQHwlo), pscale(SLOPQc, ppow(D8, 5)))
    AZ = padd(pscale(2**100, A), pneg(B))
    TN2 = pmul(pmul(PLOP, AZ), B)
    TD2 = pscale(2**56, DLO)
    TN2b = padd(pscale(2**99, TN2), pneg(TD2))
    TD2b = pscale(2**99, TD2)
    return dict(TN=TN, TD=TD, TN2b=TN2b, TD2b=TD2b)

GE = build_branch(+1)
LT = build_branch(-1)

certs = {}
EPN_ge = exp_poly_num(GE["TN"], GE["TD"], K)
certs["certGeUpLit"] = padd(
    pscale((EUD + EUN) * KF1, pmul([0, 1], ppow(GE["TD"], K + 1))),
    pscale(-S * EUD, padd(pscale(K + 1, pmul(EPN_ge, GE["TD"])),
                          pscale(2, ppow(GE["TN"], K + 1)))))
EPN2_ge = exp_poly_num(GE["TN2b"], GE["TD2b"], K)
certs["certGeLoLit"] = padd(
    pscale(EUD * S, EPN2_ge),
    pscale(-(EUD - EUN) * KF, pmul([0, 1], ppow(GE["TD2b"], K))))
EPNlt_w = exp_poly_num(LT["TN2b"], LT["TD2b"], K)
certs["certLtUpLit"] = padd(
    pscale((EUD + EUN), pmul([0, 1], EPNlt_w)),
    pscale(-EUD * S * KF, ppow(LT["TD2b"], K)))
EPNlt_t = exp_poly_num(LT["TN"], LT["TD"], K)
certs["certLtLoLit"] = padd(
    pscale(S * EUD * KF1, ppow(LT["TD"], K + 1)),
    pscale(-(EUD - EUN),
           pmul([0, 1], padd(pscale(K + 1, pmul(EPNlt_t, LT["TD"])),
                             pscale(2, ppow(LT["TN"], K + 1))))))

def peval(a, x):
    acc = 0
    for c in reversed(a):
        acc = acc * x + c
    return acc

def ptrim(a):
    # Drop high-degree zero coefficients (the trailing entries of the
    # low-degree-first list). Horner evaluation ignores them, so the trimmed
    # list agrees with the original everywhere and has a no-larger ell-1 norm;
    # the cell walks then Taylor-shift a shorter polynomial. The cert literals
    # are matched to their constructions by `evalPoly_ext` (an evaluation
    # identity), which tolerates this; the base TN/TD literals below are
    # matched by list equality and are left exactly as built.
    out = list(a)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out

# Kronecker digit width used by the proof (FloorCert*.lean `*_eval_eq` and the
# cell-walk `checkCoverK`). It must exceed log2(2 * ell1) of the certificates;
# the binding floor is the cell-walk `aeval` bound at ~2^37772 (the certificate
# coefficients are ~37k-bit and the monomials decay ~104 bits/degree, so every
# term is ~constant scale), with the eval-identity `polyL1` floor at ~2^37392.
# 38000 clears both with a ~228-bit margin; it is not a free parameter.
_B_CERT = 38000
for _name in ("certGeUpLit", "certGeLoLit", "certLtUpLit", "certLtLoLit"):
    _full = certs[_name]
    _trimmed = ptrim(_full)
    assert peval(_trimmed, 1 << _B_CERT) == peval(_full, 1 << _B_CERT), _name
    print(_name, "trimmed", len(_full), "->", len(_trimmed))
    certs[_name] = _trimmed

base = {}
for br, D in (("ge", GE), ("lt", LT)):
    for nm in ("TN", "TD", "TN2b", "TD2b"):
        base[f"{br}{nm}Lit"] = D[nm]
certs = {**base, **certs}

out = ["/-! Generated by formal/python/ln/gen_cert_literals.py — literal",
       "coefficient lists for the four main certificate polynomials. The",
       "`*_eq_lit` theorems in the certificate files verify these against",
       "the `FloorCertDefs` constructions in the kernel. -/",
       "",
       "namespace LnFloorCert",
       ""]
for name, cs in certs.items():
    out.append(f"def {name} : List Int := [")
    body = ",\n".join(f"  {c}" for c in cs)
    out.append(body + "]")
    out.append("")
    print(name, "deg", len(cs) - 1, "max coeff bits", max(abs(c).bit_length() for c in cs))
out.append("end LnFloorCert")
import os
out_path = os.path.join(os.path.dirname(__file__),
    "..", "..", "ln", "LnProof", "LnProof", "FloorCertLit.lean")
with open(os.path.abspath(out_path), "w") as f:
    f.write("\n".join(out) + "\n")
print("written")
