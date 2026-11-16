"""Native Int folds (reduce_int, reduce_int_pred_fold) as derived KernelAcceptsTcIn conversions."""
import json
import sys

import nat_ops as N
from kx import (C, app, lam, pi, bv, lit, ref, pr, spine, eq, Conv, symm, trans, chain, app_l, app_r, at_arg,
                lit_zero, lit_succ, betas, delta, iota, retype_rhs, retype_lhs, Rec, LV1, name_term)

INT = C('Int')
NAT = N.NAT
OFNAT = C('Int.ofNat')
NEGSUCC = C('Int.negSucc')
LVU = '(@ListType.cons Level (Level.param kcre_name_@@u@@) (@ListType.nil Level))'


def ilit(payload):
    return ('ilit', payload)


# kx prints unknown leaves via this hook
import kx
_orig_pr = kx.pr


def _pr(t):
    if t[0] == 'ilit':
        return '(accepts_tc_int_lit %s)' % t[1]
    return _orig_pr(t)


kx.pr = _pr
N.pr = _pr
pr = _pr

# ---------------------------------------------------------------- Int.rec canonical data (hand; the emit
# mode reflects it from the live environment at registration and the proofs are re-checked against it)
INTREC_RHS_OFNAT = lam(pi(INT, ('sort', '(Level.param kcre_name_@@u@@)')),
                       lam(pi(NAT, app(bv(1), app(OFNAT, bv(0)))),
                           lam(pi(NAT, app(bv(2), app(NEGSUCC, bv(0)))),
                               lam(NAT, app(bv(2), bv(0))))))
INTREC_RHS_NEGSUCC = lam(pi(INT, ('sort', '(Level.param kcre_name_@@u@@)')),
                         lam(pi(NAT, app(bv(1), app(OFNAT, bv(0)))),
                             lam(pi(NAT, app(bv(2), app(NEGSUCC, bv(0)))),
                                 lam(NAT, app(bv(1), bv(0))))))
INTREC = Rec('Int.rec', 'accepts_tc_int_rec_meta',
             {'Int.ofNat': (1, INTREC_RHS_OFNAT), 'Int.negSucc': (1, INTREC_RHS_NEGSUCC)},
             'kcre_name_@@u@@', 'hmi', {'Int.ofNat': 'hio', 'Int.negSucc': 'hin'})
INTREC.prefix = 3
INTREC_RULES = {'Int.ofNat': 'accepts_tc_int_rec_ofnat_rule', 'Int.negSucc': 'accepts_tc_int_rec_negsucc_rule'}
P_INTREC = ('(hmi : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) kcre_name_@@Int.rec@@) '
            '(@OptionType.some RecMeta accepts_tc_int_rec_meta)) '
            '(hio : @Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Int.rec@@ kcre_name_@@Int.ofNat@@) '
            '(@OptionType.some RecRule accepts_tc_int_rec_ofnat_rule)) '
            '(hin : @Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Int.rec@@ kcre_name_@@Int.negSucc@@) '
            '(@OptionType.some RecRule accepts_tc_int_rec_negsucc_rule))')
A_INTREC = 'hmi hio hin'


def intrec_app(M, a, b, major, *extras):
    return app(C('Int.rec', LV1), M, a, b, major, *extras)


def iota_int(e):
    return iota(e, INTREC, '(Level.succ Level.zero)', INTREC_RULES)


ITEMS = N.ITEMS
INT_CLOSURE = {}
NAT_NEEDS = {}
INT_ORDER = ['Int.neg', 'Int.negOfNat', 'Int.subNatNat', 'Int.add', 'Int.sub', 'Int.mul', 'Int.toNat']


def ihyp(op):
    return 'h_' + op.replace('.', '_').lower()


def ibody_const(op):
    return 'accepts_tc_%s_body' % op.replace('.', '_').lower()


def ip_body(op):
    return '(%s : @Eq (OptionType KExpr) (kdef_value_at (red_def R) kcre_name_@@%s@@ (@ListType.nil Level)) (@OptionType.some KExpr %s))' % (
        ihyp(op), op, ibody_const(op))


def ilemma(op):
    return 'kernel_accepts_tc_in_%s_fold' % op.replace('.', '_').lower()


def iprem_decl(op):
    nat = sorted(NAT_NEEDS.get(op, []), key=N.ORDER.index)
    ints = sorted(INT_CLOSURE[op], key=INT_ORDER.index)
    return ' '.join([N.P_NATREC, P_INTREC] + [N.p_body(o) for o in nat] + [ip_body(o) for o in ints])


def iprem_args(op):
    nat = sorted(NAT_NEEDS.get(op, []), key=N.ORDER.index)
    ints = sorted(INT_CLOSURE[op], key=INT_ORDER.index)
    return ' '.join([N.A_NATREC, A_INTREC] + [N.hyp(o) for o in nat] + [ihyp(o) for o in ints])


def icall(op, args, kinds, result):
    """args: payload strings; kinds: 'n' (literal) / 'i' (int literal)"""
    lhs = app(C(op), *[lit(a) if k == 'n' else ilit(a) for a, k in zip(args, kinds)])
    return Conv(lhs, result, '(%s R tenv G %s %s)' % (ilemma(op), ' '.join(args), iprem_args(op)))


def iregister(op, binders, whole):
    ty = 'forall %s %s %s, %s' % (N.HDR, binders, iprem_decl(op), whole.ty())
    N.add_thm(ilemma(op), ty, 'fun %s %s %s => %s' % (N.HDR, binders, iprem_decl(op), whole.proof))


def int_rec_proof(var, motive_ty, ofnat_var, ofnat_case, negsucc_var, negsucc_case):
    return '(@Int.rec (fun (%s : Int) => %s) (fun (%s : Nat) => %s) (fun (%s : Nat) => %s) %s)' % (
        var, motive_ty(var), ofnat_var, ofnat_case, negsucc_var, negsucc_case, var)


BODIES = {}
INTINT = lam(INT, INT)
# Int.neg i := Int.rec (fun _ => Int) (fun n => Nat.rec (fun _ => Int) (ofNat zero) (fun n1 _ => negSucc n1) n)
#                                    (fun n => ofNat (succ n)) i
BODIES['Int.neg'] = lam(INT, intrec_app(INTINT,
                                        lam(NAT, N.natrec_app(lam(NAT, INT), app(OFNAT, N.ZERO), lam(NAT, lam(INT, app(NEGSUCC, bv(1)))), bv(0))),
                                        lam(NAT, app(OFNAT, app(N.SUCC, bv(0)))), bv(0)))
BODIES['Int.negOfNat'] = lam(NAT, N.natrec_app(lam(NAT, INT), app(OFNAT, N.ZERO), lam(NAT, lam(INT, app(NEGSUCC, bv(1)))), bv(0)))
PRED_STEP = lam(NAT, lam(INT, intrec_app(INTINT,
                                         lam(NAT, N.natrec_app(lam(NAT, INT), app(NEGSUCC, N.ZERO), lam(NAT, lam(INT, app(OFNAT, bv(1)))), bv(0))),
                                         lam(NAT, app(NEGSUCC, app(N.SUCC, bv(0)))), bv(0))))
BODIES['Int.subNatNat'] = lam(NAT, lam(NAT, N.natrec_app(lam(NAT, INT), app(OFNAT, bv(1)), PRED_STEP, bv(0))))
INT2 = pi(INT, INT)
ADD_OO = lam(NAT, app(OFNAT, app(C('Nat.add'), bv(2), bv(0))))
ADD_ON = lam(NAT, app(C('Int.subNatNat'), bv(2), app(N.SUCC, bv(0))))
ADD_NO = lam(NAT, app(C('Int.subNatNat'), bv(0), app(N.SUCC, bv(2))))
ADD_NN = lam(NAT, app(NEGSUCC, app(N.SUCC, app(C('Nat.add'), bv(2), bv(0)))))
BODIES['Int.add'] = lam(INT, lam(INT, intrec_app(lam(INT, INT2),
                                                 lam(NAT, lam(INT, intrec_app(INTINT, ADD_OO, ADD_ON, bv(0)))),
                                                 lam(NAT, lam(INT, intrec_app(INTINT, ADD_NO, ADD_NN, bv(0)))),
                                                 bv(1), bv(0))))
BODIES['Int.sub'] = lam(INT, lam(INT, app(C('Int.add'), bv(1), app(C('Int.neg'), bv(0)))))
MUL_OO = lam(NAT, app(OFNAT, app(C('Nat.mul'), bv(2), bv(0))))
MUL_ON = lam(NAT, app(C('Int.negOfNat'), app(C('Nat.mul'), bv(2), app(N.SUCC, bv(0)))))
MUL_NO = lam(NAT, app(C('Int.negOfNat'), app(C('Nat.mul'), app(N.SUCC, bv(2)), bv(0))))
MUL_NN = lam(NAT, app(OFNAT, app(C('Nat.mul'), app(N.SUCC, bv(2)), app(N.SUCC, bv(0)))))
BODIES['Int.mul'] = lam(INT, lam(INT, intrec_app(lam(INT, INT2),
                                                 lam(NAT, lam(INT, intrec_app(INTINT, MUL_OO, MUL_ON, bv(0)))),
                                                 lam(NAT, lam(INT, intrec_app(INTINT, MUL_NO, MUL_NN, bv(0)))),
                                                 bv(1), bv(0))))


def ibody(op):
    b = BODIES[op]
    if N.MODE['emit']:
        ITEMS.append({'kind': 'reflect_body', 'name': ibody_const(op), 'of': op})
    else:
        N.add_def('def %s : KExpr := %s' % (ibody_const(op), pr(b)), ibody_const(op))
    return ref(ibody_const(op), b)


def ctor_lit(ctor, payload):
    return app(OFNAT if ctor == 'ofNat' else NEGSUCC, lit(payload))


# ---------------------------------------------------------------- Int.toNat (data_types_nat): an Int.rec to a
# Nat literal. `Int.toNat i := Int.rec (fun _ => Nat) (fun n => n) (fun _ => Nat.zero) i`, so on either
# constructor literal it iota-reduces to the payload (ofNat) or to `Nat.zero` (negSucc).
BODIES['Int.toNat'] = lam(INT, intrec_app(lam(INT, NAT), lam(NAT, bv(0)), lam(NAT, N.ZERO), bv(0)))


def gen_tonat():
    op = 'Int.toNat'
    INT_CLOSURE[op] = [op]
    b = ibody(op)

    def case_proof(cx, out):
        fr = front(op, b, [ctor_lit(cx, 'n')])  # delta + 1 beta -> Int.rec .. (Int.cx (lit n))
        i1 = iota_int(fr.rhs)
        # the rule's right side over motive, both minors and the field (4), then the minor itself (1)
        i2 = betas(i1.rhs, 5)
        steps = [fr, i1, i2]
        if cx == 'negSucc':
            assert eq(i2.rhs, N.ZERO), pr(i2.rhs)
            steps.append(symm(lit_zero()))
        else:
            assert eq(i2.rhs, lit('n')), pr(i2.rhs)
        c = retype_rhs(chain(steps), out)
        return retype_lhs(c, app(C(op), ctor_lit(cx, 'n'))).proof

    def mot(iv):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(app(C(op), ilit(iv))), pr(lit('(Int.toNat %s)' % iv)))
    rec = int_rec_proof('i', mot, 'n', case_proof('ofNat', lit('n')),
                        'n', case_proof('negSucc', lit('Nat.zero')))
    whole = Conv(app(C(op), ilit('i')), lit('(Int.toNat i)'), rec)
    iregister(op, '(i : Int)', whole)


def base():
    N.add_def('def accepts_tc_int_lit (i : Int) : KExpr := @Int.rec (fun (_ : Int) => KExpr) '
              '(fun (n : Nat) => KExpr.app (KExpr.const kcre_name_@@Int.ofNat@@ (@ListType.nil Level)) (literal_nat n)) '
              '(fun (n : Nat) => KExpr.app (KExpr.const kcre_name_@@Int.negSucc@@ (@ListType.nil Level)) (literal_nat n)) i',
              'accepts_tc_int_lit')
    if N.MODE['emit']:
        ITEMS.append({'kind': 'reflect_rec', 'of': 'Int.rec', 'meta': 'accepts_tc_int_rec_meta',
                      'rules': {'Int.ofNat': 'accepts_tc_int_rec_ofnat_rule', 'Int.negSucc': 'accepts_tc_int_rec_negsucc_rule'}})
    else:
        N.add_def('def accepts_tc_int_rec_meta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) Nat.zero Bool.true '
                  '(KConstSig.mk (@ListType.cons Name kcre_name_@@u@@ (@ListType.nil Name)) (KExpr.sort Level.zero))' + (' Nat.zero' if N.MODE.get('kflag') else ''),
                  'accepts_tc_int_rec_meta')
        N.add_def('def accepts_tc_int_rec_ofnat_rule : RecRule := RecRule.mk kcre_name_@@Int.ofNat@@ (Nat.succ Nat.zero) %s' % pr(INTREC_RHS_OFNAT),
                  'accepts_tc_int_rec_ofnat_rule')
        N.add_def('def accepts_tc_int_rec_negsucc_rule : RecRule := RecRule.mk kcre_name_@@Int.negSucc@@ (Nat.succ Nat.zero) %s' % pr(INTREC_RHS_NEGSUCC),
                  'accepts_tc_int_rec_negsucc_rule')
    from kx import inst_levels
    for nm, rhs in (('accepts_tc_int_rec_ofnat_rhs1', INTREC_RHS_OFNAT), ('accepts_tc_int_rec_negsucc_rhs1', INTREC_RHS_NEGSUCC)):
        t = inst_levels(rhs, 'kcre_name_@@u@@', '(Level.succ Level.zero)')
        N.add_def('def %s : KExpr := %s' % (nm, pr(t)), nm)
        name_term(nm, t)


def front(op, b, args):
    e0 = app(C(op), *args)
    c1 = delta(e0, op, b, ihyp(op))
    return trans(c1, betas(c1.rhs, len(args)))


# ---------------------------------------------------------------- Int.negOfNat, Int.neg
def gen_negofnat():
    op = 'Int.negOfNat'
    INT_CLOSURE[op] = [op]
    b = ibody(op)
    fr = front(op, b, [lit('x')])
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]

    def lhs(v):
        return N.natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(ilit('(Int.negOfNat %s)' % v)))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    c4 = app_r(OFNAT, symm(lit_zero()))
    base_ = retype_rhs(chain([c1, c2, c3, c4]), ilit('(Int.negOfNat Nat.zero)'))
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ k)'), 'k')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    assert eq(d3.rhs, ctor_lit('negSucc', 'k')), pr(d3.rhs)
    step = retype_rhs(chain([d1, d2, d3]), ilit('(Int.negOfNat (Nat.succ k))'))
    rec = N.nat_rec_proof('x', mot, base_.proof, 'k', '_ih', step.proof)
    iregister(op, '(x : Nat)', trans(fr, Conv(fr.rhs, ilit('(Int.negOfNat x)'), rec)))


def gen_neg():
    op = 'Int.neg'
    INT_CLOSURE[op] = [op]
    b = ibody(op)

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(app(C(op), ilit(v))), pr(ilit('(Int.neg %s)' % v)))
    # ofNat n
    fr = front(op, b, [ctor_lit('ofNat', 'n')])
    c2 = iota_int(fr.rhs)
    c3 = betas(c2.rhs, 5)
    inner = c3.rhs
    ih_, iargs = spine(inner)
    IM, IZ, IS = iargs[0], iargs[1], iargs[2]

    def nmot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(N.natrec_app(IM, IZ, IS, lit(v))), pr(ilit('(Int.neg (Int.ofNat %s))' % v)))
    f1 = N.major_to_ctor_zero(N.natrec_app(IM, IZ, IS, lit('Nat.zero')))
    f2 = N.iota_nat(f1.rhs)
    f3 = betas(f2.rhs, 3)
    f4 = app_r(OFNAT, symm(lit_zero()))
    nb = retype_rhs(chain([f1, f2, f3, f4]), ilit('(Int.neg (Int.ofNat Nat.zero))'))
    g1 = N.major_to_ctor_succ(N.natrec_app(IM, IZ, IS, lit('(Nat.succ j)')), 'j')
    g2 = N.iota_nat(g1.rhs)
    g3 = betas(g2.rhs, 6)
    ns = retype_rhs(chain([g1, g2, g3]), ilit('(Int.neg (Int.ofNat (Nat.succ j)))'))
    nrec = N.nat_rec_proof('n', nmot, nb.proof, 'j', '_jh', ns.proof)
    ofnat_case = retype_lhs(trans(chain([fr, c2, c3]), Conv(inner, ilit('(Int.neg (Int.ofNat n))'), nrec)),
                            app(C(op), ilit('(Int.ofNat n)')))
    # negSucc n
    fr2 = front(op, b, [ctor_lit('negSucc', 'n')])
    e2 = iota_int(fr2.rhs)
    e3 = betas(e2.rhs, 5)
    assert eq(e3.rhs, app(OFNAT, app(N.SUCC, lit('n')))), pr(e3.rhs)
    e4 = app_r(OFNAT, symm(lit_succ('n')))
    neg_case = retype_lhs(retype_rhs(chain([fr2, e2, e3, e4]), ilit('(Int.neg (Int.negSucc n))')),
                          app(C(op), ilit('(Int.negSucc n)')))
    rec = int_rec_proof('i', mot, 'n', ofnat_case.proof, 'n', neg_case.proof)
    whole = Conv(app(C(op), ilit('i')), ilit('(Int.neg i)'), rec)
    iregister(op, '(i : Int)', whole)


# ---------------------------------------------------------------- the Int predecessor step (subNatNat's step and
# the pinned reduce_int_pred_fold step): Int.rec on an int literal
def pred_step_meta(v):
    return ('(@Int.rec (fun (_ : Int) => Int) (fun (n3 : Nat) => @Nat.rec (fun (_ : Nat) => Int) (Int.negSucc Nat.zero) '
            '(fun (n4 : Nat) (_ : Int) => Int.ofNat n4) n3) (fun (n3 : Nat) => Int.negSucc (Nat.succ n3)) %s)' % v)


def gen_pred_select():
    """Int.rec (fun _ => Int) C1 C2 (intlit v) == intlit (<the same step on v>)"""
    body = PRED_STEP[2][2]  # Int.rec INTINT C1 C2 (bv 0) under the two binders
    head, args = spine(body)
    M, c1, c2 = args[0], args[1], args[2]
    N.name_param('accepts_tc_int_pred_ofnat_case', c1, [])
    N.name_param('accepts_tc_int_pred_negsucc_case', c2, [])
    N.name_param('accepts_tc_int_pred_step', PRED_STEP, [])

    def lhs(major):
        return intrec_app(M, c1, c2, major)

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(ilit(v))), pr(ilit(pred_step_meta(v))))
    # ofNat n: iota -> C1 (lit n) -> Nat.rec on lit n
    e = lhs(ctor_lit('ofNat', 'n'))
    a1 = iota_int(e)
    a2 = betas(a1.rhs, 5)
    inner = a2.rhs
    ih_, iargs = spine(inner)
    IM, IZ, IS = iargs[0], iargs[1], iargs[2]

    def nmot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(N.natrec_app(IM, IZ, IS, lit(v))), pr(ilit(pred_step_meta('(Int.ofNat %s)' % v))))
    f1 = N.major_to_ctor_zero(N.natrec_app(IM, IZ, IS, lit('Nat.zero')))
    f2 = N.iota_nat(f1.rhs)
    f3 = betas(f2.rhs, 3)
    f4 = app_r(NEGSUCC, symm(lit_zero()))
    nb = retype_rhs(chain([f1, f2, f3, f4]), ilit(pred_step_meta('(Int.ofNat Nat.zero)')))
    g1 = N.major_to_ctor_succ(N.natrec_app(IM, IZ, IS, lit('(Nat.succ j)')), 'j')
    g2 = N.iota_nat(g1.rhs)
    g3 = betas(g2.rhs, 6)
    assert eq(g3.rhs, ctor_lit('ofNat', 'j')), pr(g3.rhs)
    ns = retype_rhs(chain([g1, g2, g3]), ilit(pred_step_meta('(Int.ofNat (Nat.succ j))')))
    nrec = N.nat_rec_proof('n', nmot, nb.proof, 'j', '_jh', ns.proof)
    ofnat_case = retype_lhs(trans(chain([a1, a2]), Conv(inner, ilit(pred_step_meta('(Int.ofNat n)')), nrec)),
                            lhs(ilit('(Int.ofNat n)')))
    e = lhs(ctor_lit('negSucc', 'n'))
    b1 = iota_int(e)
    b2 = betas(b1.rhs, 5)
    assert eq(b2.rhs, app(NEGSUCC, app(N.SUCC, lit('n')))), pr(b2.rhs)
    b3 = app_r(NEGSUCC, symm(lit_succ('n')))
    neg_case = retype_lhs(retype_rhs(chain([b1, b2, b3]), ilit(pred_step_meta('(Int.negSucc n)'))),
                          lhs(ilit('(Int.negSucc n)')))
    rec = int_rec_proof('v', mot, 'n', ofnat_case.proof, 'n', neg_case.proof)
    ty = 'forall %s (v : Int) %s %s, %s' % (N.HDR, N.P_NATREC, P_INTREC, mot('v'))
    N.add_thm('accepts_tc_int_pred_step_select', ty, 'fun %s (v : Int) %s %s => %s' % (N.HDR, N.P_NATREC, P_INTREC, rec))
    return lambda v: Conv(lhs(ilit(v)), ilit(pred_step_meta(v)),
                          '(accepts_tc_int_pred_step_select R tenv G %s %s %s)' % (v, N.A_NATREC, A_INTREC))


PRED_SELECT = None


def gen_subnatnat():
    global PRED_SELECT
    op = 'Int.subNatNat'
    INT_CLOSURE[op] = [op]
    PRED_SELECT = gen_pred_select()
    b = ibody(op)
    fr = front(op, b, [lit('m'), lit('n')])
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]

    def lhs(v):
        return N.natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(ilit('(Int.subNatNat m %s)' % v)))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    assert eq(c3.rhs, ctor_lit('ofNat', 'm')), pr(c3.rhs)
    base_ = retype_rhs(chain([c1, c2, c3]), ilit('(Int.subNatNat m Nat.zero)'))
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ k)'), 'k')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    # Int.rec INTINT C1 C2 (REC (lit k)) -> IH at the major
    d4 = at_arg(d3.rhs, 3, retype_lhs(Conv(lhs('k'), ilit('(Int.subNatNat m k)'), 'ih'), lhs('k')))
    d5 = PRED_SELECT('(Int.subNatNat m k)')
    step = retype_rhs(chain([d1, d2, d3, d4, d5]), ilit('(Int.subNatNat m (Nat.succ k))'))
    rec = N.nat_rec_proof('n', mot, base_.proof, 'k', 'ih', step.proof)
    iregister(op, '(m : Nat) (n : Nat)', trans(fr, Conv(fr.rhs, ilit('(Int.subNatNat m n)'), rec)))
