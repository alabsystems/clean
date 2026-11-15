"""Bitwise native folds (Nat.land / lor / xor / shiftRight) as derived KernelAcceptsTcIn conversions."""
import json
import sys

import nat_ops as N
import kx
from kx import (C, app, lam, pi, bv, lit, blit, ref, spine, eq, Conv, symm, trans, chain, app_l, app_r, at_arg,
                lit_zero, lit_succ, betas, delta, iota, retype_rhs, retype_lhs, Rec, LV1, name_term)
import canon

_orig_pr = kx.pr


def _pr(t):
    if t[0] == 'plit':
        return '(accepts_tc_nat_pair_lit %s)' % t[1]
    return _orig_pr(t)


kx.pr = _pr
N.pr = _pr
pr = _pr

NAT, ZERO, SUCC = N.NAT, N.ZERO, N.SUCC
BOOL, TRUE, FALSE = C('Bool'), C('Bool.true'), C('Bool.false')
LV00 = '(ListType.cons Level Level.zero (ListType.cons Level Level.zero (ListType.nil Level)))'
PROD = app(C('Prod', LV00), NAT, NAT)
PRODMK = C('Prod.mk', LV00)
FST = C('Prod.fst', LV00)
SND = C('Prod.snd', LV00)
ADD, SUB = C('Nat.add'), C('Nat.sub')
SORT1 = ('sort', '(Level.succ Level.zero)')


def plit(payload):
    return ('plit', payload)


def pair(a, b):
    return app(PRODMK, NAT, NAT, a, b)


def boolrec_app(M, f, t, major, *extras):
    return app(C('Bool.rec', LV1), M, f, t, major, *extras)


# ---------------------------------------------------------------- Bool.rec canonical data (the reflected seed's)
def _rule(ctor):
    nf, rhs = canon.rule_rhs(N.NAME2TAG['Bool.rec'] if hasattr(N, 'NAME2TAG') else kx.NAME2TAG['Bool.rec'], ctor)
    return nf, rhs


BR_F = _rule('Bool.false')
BR_T = _rule('Bool.true')
BOOLREC = Rec('Bool.rec', 'kcre_rec_meta_@@Bool.rec@@', {'Bool.false': BR_F, 'Bool.true': BR_T},
              'kcre_name_@@u@@', 'hbm', {'Bool.false': 'hbf', 'Bool.true': 'hbt'})
BOOLREC.prefix = 3
BOOLREC_RULES = {'Bool.false': 'accepts_tc_bool_rec_false_rule', 'Bool.true': 'accepts_tc_bool_rec_true_rule'}
P_BOOLREC = ('(hbm : Eq (OptionType RecMeta) (recmeta_for (red_rec R) kcre_name_@@Bool.rec@@) '
             '(OptionType.some RecMeta kcre_rec_meta_@@Bool.rec@@)) '
             '(hbf : Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Bool.rec@@ kcre_name_@@Bool.false@@) '
             '(OptionType.some RecRule accepts_tc_bool_rec_false_rule)) '
             '(hbt : Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Bool.rec@@ kcre_name_@@Bool.true@@) '
             '(OptionType.some RecRule accepts_tc_bool_rec_true_rule))')
A_BOOLREC = 'hbm hbf hbt'
P_PRODMK = ('(cm : KCtorMeta) (hpm : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) kcre_name_@@Prod.mk@@) '
            '(OptionType.some KCtorMeta cm)) (hpn : Eq Nat (kctor_num_params cm) (Nat.succ (Nat.succ Nat.zero)))')
A_PRODMK = 'cm hpm hpn'


def iota_bool(e):
    return iota(e, BOOLREC, '(Level.succ Level.zero)', BOOLREC_RULES)


ITEMS = N.ITEMS

# ---------------------------------------------------------------- canonical bodies (hand; reflected at registration)
BODIES = {}
BODIES['Prod.fst'] = lam(SORT1, lam(SORT1, lam(app(C('Prod', LV00), bv(1), bv(0)), ('proj', 'kcre_name_@@Prod@@', 0, bv(0)))))
BODIES['Prod.snd'] = lam(SORT1, lam(SORT1, lam(app(C('Prod', LV00), bv(1), bv(0)), ('proj', 'kcre_name_@@Prod@@', 1, bv(0)))))
BODIES['Nat.div2Pair'] = lam(NAT, N.natrec_app(
    lam(NAT, PROD), pair(ZERO, ZERO),
    lam(NAT, lam(PROD, pair(app(ADD, app(FST, NAT, NAT, bv(0)), app(SND, NAT, NAT, bv(0))),
                            app(SUB, app(SUCC, ZERO), app(SND, NAT, NAT, bv(0)))))), bv(0)))
BODIES['Nat.div2'] = lam(NAT, app(FST, NAT, NAT, app(C('Nat.div2Pair'), bv(0))))
BODIES['Nat.div2Par'] = lam(NAT, app(SND, NAT, NAT, app(C('Nat.div2Pair'), bv(0))))
BODIES['Nat.iterDiv2'] = lam(NAT, N.natrec_app(lam(NAT, pi(NAT, NAT)), lam(NAT, bv(0)),
                                               lam(NAT, lam(pi(NAT, NAT), lam(NAT, app(bv(1), app(C('Nat.div2'), bv(0)))))), bv(0)))
BODIES['Nat.shiftRight'] = lam(NAT, lam(NAT, app(C('Nat.iterDiv2'), bv(0), bv(1))))
BODIES['Nat.toBoolPar'] = lam(NAT, N.natrec_app(lam(NAT, BOOL), FALSE, lam(NAT, lam(BOOL, TRUE)), bv(0)))
BODIES['Nat.testBit'] = lam(NAT, lam(NAT, app(C('Nat.toBoolPar'), app(C('Nat.div2Par'), app(C('Nat.iterDiv2'), bv(0), bv(1))))))
BODIES['Nat.ofBool'] = lam(BOOL, boolrec_app(lam(BOOL, NAT), ZERO, app(SUCC, ZERO), bv(0)))
BODIES['Bool.not'] = lam(BOOL, boolrec_app(lam(BOOL, BOOL), TRUE, FALSE, bv(0)))
BODIES['Bool.and'] = lam(BOOL, lam(BOOL, boolrec_app(lam(BOOL, BOOL), FALSE, bv(0), bv(1))))
BODIES['Bool.or'] = lam(BOOL, lam(BOOL, boolrec_app(lam(BOOL, BOOL), bv(0), TRUE, bv(1))))
BODIES['Bool.xor'] = lam(BOOL, lam(BOOL, boolrec_app(lam(BOOL, BOOL), bv(0), app(C('Bool.not'), bv(0)), bv(1))))
BB2 = pi(BOOL, pi(BOOL, BOOL))
NN2 = pi(NAT, pi(NAT, NAT))
_R = app(bv(2), app(C('Nat.div2'), bv(1)), app(C('Nat.div2'), bv(0)))
STEPBODY = app(ADD, app(ADD, _R, _R), app(C('Nat.ofBool'), app(bv(5), app(C('Nat.testBit'), bv(1), ZERO),
                                                                   app(C('Nat.testBit'), bv(0), ZERO))))
BODIES['Nat.bitwiseAux'] = lam(BB2, lam(NAT, N.natrec_app(lam(NAT, NN2), lam(NAT, lam(NAT, ZERO)),
                                                          lam(NAT, lam(NN2, lam(NAT, lam(NAT, STEPBODY)))), bv(0))))
BODIES['Nat.bitwise'] = lam(BB2, lam(NAT, lam(NAT, app(C('Nat.bitwiseAux'), bv(2), app(ADD, bv(1), bv(0)), bv(1), bv(0)))))
for _op, _f in (('Nat.land', 'Bool.and'), ('Nat.lor', 'Bool.or'), ('Nat.xor', 'Bool.xor')):
    BODIES[_op] = lam(NAT, lam(NAT, app(C('Nat.bitwise'), C(_f), bv(1), bv(0))))

LEVELS = {'Prod.fst': LV00, 'Prod.snd': LV00}
ORDER = ['Nat.add', 'Nat.sub', 'Nat.pred', 'Prod.fst', 'Prod.snd', 'Nat.div2Pair', 'Nat.div2', 'Nat.div2Par',
         'Nat.iterDiv2', 'Nat.shiftRight', 'Nat.toBoolPar', 'Nat.testBit', 'Nat.ofBool', 'Bool.not', 'Bool.and',
         'Bool.or', 'Bool.xor', 'Nat.bitwiseAux', 'Nat.bitwise', 'Nat.land', 'Nat.lor', 'Nat.xor']
CLOSURE = {}
NEEDS = {}  # op -> set of extra keys: 'bool', 'prod'


def bhyp(op):
    return 'h_' + op.replace('.', '_').lower()


def bbody_const(op):
    return 'accepts_tc_%s_body' % op.replace('.', '_').lower()


def bp_body(op):
    if op in ('Nat.add', 'Nat.sub', 'Nat.pred'):
        return N.p_body(op)
    return '(%s : Eq (OptionType KExpr) (kdef_value_at (red_def R) kcre_name_@@%s@@ %s) (OptionType.some KExpr %s))' % (
        bhyp(op), op, LEVELS.get(op, '(ListType.nil Level)'), bbody_const(op))


def bh(op):
    return N.hyp(op) if op in ('Nat.add', 'Nat.sub', 'Nat.pred') else bhyp(op)


def blemma(op):
    return 'kernel_accepts_tc_in_%s_fold' % op.replace('.', '_').lower()


def closure(op):
    seen = []

    def go(o):
        for d in CLOSURE[o]:
            if d not in seen:
                seen.append(d)
                if d != o and d in CLOSURE:
                    go(d)
    go(op)
    return sorted(seen, key=ORDER.index)


def needs(op):
    out = set()
    for o in closure(op):
        out |= NEEDS.get(o, set())
    return out


def bprem_decl(op):
    parts = [N.P_NATREC]
    if 'bool' in needs(op):
        parts.append(P_BOOLREC)
    if 'prod' in needs(op):
        parts.append(P_PRODMK)
    return ' '.join(parts + [bp_body(o) for o in closure(op)])


def bprem_args(op):
    parts = [N.A_NATREC]
    if 'bool' in needs(op):
        parts.append(A_BOOLREC)
    if 'prod' in needs(op):
        parts.append(A_PRODMK)
    return ' '.join(parts + [bh(o) for o in closure(op)])


def bcall(op, args, lhs, rhs):
    return Conv(lhs, rhs, '(%s R tenv G %s %s)' % (blemma(op), ' '.join(args), bprem_args(op)))


# each lemma's premises as registered: CLOSURE['Nat.bitwise'] / ['Nat.bitwiseAux'] are re-set per
# connective, so a witness instance reads this snapshot, never the table after the loop
REGISTERED = {}


def bregister(op, binders, whole):
    REGISTERED[op] = (closure(op), needs(op))
    ty = 'forall %s %s %s, %s' % (N.HDR, binders, bprem_decl(op), whole.ty())
    N.add_thm(blemma(op), ty, 'fun %s %s %s => %s' % (N.HDR, binders, bprem_decl(op), whole.proof))


def bbody(op):
    b = BODIES[op]
    if N.MODE['emit']:
        item = {'kind': 'reflect_body', 'name': bbody_const(op), 'of': op}
        if op in LEVELS:
            item['zero_levels'] = 2
        ITEMS.append(item)
    else:
        N.add_def('def %s : KExpr := %s' % (bbody_const(op), pr(b)), bbody_const(op))
    return ref(bbody_const(op), b)


def bfront(op, b, args):
    e0 = app(C(op, LEVELS.get(op, kx.NIL_LV)), *args)
    c1 = delta(e0, op, b, bhyp(op))
    nlam = 0
    t = kx.unref(b)
    while t[0] == 'lam' and nlam < len(args):
        nlam += 1
        t = t[2]
    return trans(c1, betas(c1.rhs, nlam))


def at_path(term, path, c):
    if not path:
        assert eq(term, c.lhs), (pr(term), pr(c.lhs))
        return c
    head, args = spine(kx.unref(term))
    inner = at_path(args[path[0]], path[1:], c)
    return at_arg(term, path[0], inner)


def bool_case(var, mot, false_proof, true_proof):
    return '(Bool.rec (fun (%s : Bool) => %s) (%s) (%s) %s)' % (var, mot(var), false_proof, true_proof, var)


# ---------------------------------------------------------------- helpers registered once
def base():
    N.add_def('def accepts_tc_nat_pair_lit (p : Prod Nat Nat) : KExpr := KExpr.app (KExpr.app (KExpr.app (KExpr.app '
              '(KExpr.const kcre_name_@@Prod.mk@@ %s) (KExpr.const kcre_name_@@Nat@@ (ListType.nil Level))) '
              '(KExpr.const kcre_name_@@Nat@@ (ListType.nil Level))) (literal_nat (Prod.fst Nat Nat p))) '
              '(literal_nat (Prod.snd Nat Nat p))' % LV00, 'accepts_tc_nat_pair_lit')
    for ctor, (nf, rhs) in (('Bool.false', BR_F), ('Bool.true', BR_T)):
        const = BOOLREC_RULES[ctor]
        N.add_def('def %s : RecRule := RecRule.mk kcre_name_@@%s@@ kcre_nat_%d %s' % (const, ctor, nf, pr(rhs)), const)
        N.add_thm(const + '_reflected',
                  'Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) kcre_name_@@Bool.rec@@ kcre_name_@@%s@@) (OptionType.some RecRule %s)' % (ctor, const),
                  'Eq.refl (OptionType RecRule) (OptionType.some RecRule %s)' % const)
    from kx import inst_levels
    for nm, (nf, rhs) in (('accepts_tc_bool_rec_false_rhs1', BR_F), ('accepts_tc_bool_rec_true_rhs1', BR_T)):
        t = inst_levels(rhs, 'kcre_name_@@u@@', '(Level.succ Level.zero)')
        N.add_def('def %s : KExpr := %s' % (nm, pr(t)), nm)
        name_term(nm, t)
    # projection of a Prod.mk application: the projection-beta step, over R's constructor table
    ty = ('forall %s (cm : KCtorMeta) (hpm : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) kcre_name_@@Prod.mk@@) (OptionType.some KCtorMeta cm)) '
          '(hpn : Eq Nat (kctor_num_params cm) (Nat.succ (Nat.succ Nat.zero))) (us : ListType Level) (A : KExpr) (B : KExpr) (a : KExpr) (b : KExpr) (i : Nat), '
          'KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj kcre_name_@@Prod@@ i (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const kcre_name_@@Prod.mk@@ us) A) B) a) b)) '
          '(OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) (KExpr.sort Level.zero) (fun (x : KExpr) => x) '
          '(list_head (list_drop i (ListType.cons KExpr a (ListType.cons KExpr b (ListType.nil KExpr))))))') % N.HDR
    # proved per index below; the general form needs the Option read-off, so register the two used indices directly
    for idx, fld in ((0, 'a'), (1, 'b')):
        sub = '(KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const kcre_name_@@Prod.mk@@ us) A) B) a) b)'
        e = '(KExpr.proj kcre_name_@@Prod@@ kcre_nat_%d %s)' % (idx, sub)
        sel_ty = ('Eq (OptionType KExpr) (list_head (list_drop (Nat.add (kctor_num_params cm) kcre_nat_%d) (kapp_args %s))) (OptionType.some KExpr %s)' % (idx, sub, fld))
        sel_goal = ('Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.succ (Nat.succ Nat.zero)) kcre_nat_%d) (kapp_args %s))) (OptionType.some KExpr %s)' % (idx, sub, fld))
        selected = ('(Eq.substType Nat (fun (k : Nat) => Eq (OptionType KExpr) (list_head (list_drop (Nat.add k kcre_nat_%d) (kapp_args %s))) (OptionType.some KExpr %s)) '
                    '(Nat.succ (Nat.succ Nat.zero)) (kctor_num_params cm) (Eq.symm Nat (kctor_num_params cm) (Nat.succ (Nat.succ Nat.zero)) hpn) '
                    '(Eq.refl (OptionType KExpr) (OptionType.some KExpr %s)))') % (idx, sub, fld, fld)
        proof = ('KernelAcceptsTcIn.cdp R tenv G %s %s (DefEqCDPIn.raw R %s %s (par_reduces_cdp.projection_beta R kcre_name_@@Prod@@ kcre_nat_%d %s %s '
                 '(Eq.trans (OptionType KExpr) (projection_post_whnf_reduct R %s) (projection_post_whnf_field R kcre_nat_%d %s) (OptionType.some KExpr %s) '
                 '(projection_post_whnf_proj R kcre_name_@@Prod@@ kcre_nat_%d %s) '
                 '(projection_post_whnf_field_intro R kcre_nat_%d %s kcre_name_@@Prod.mk@@ cm %s (Eq.refl (OptionType Name) (OptionType.some Name kcre_name_@@Prod.mk@@)) hpm %s))))') % (
            e, fld, e, fld, idx, sub, fld, e, idx, sub, fld, idx, sub, idx, sub, fld, selected)
        ty_i = ('forall %s (cm : KCtorMeta) (hpm : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) kcre_name_@@Prod.mk@@) (OptionType.some KCtorMeta cm)) '
                '(hpn : Eq Nat (kctor_num_params cm) (Nat.succ (Nat.succ Nat.zero))) (us : ListType Level) (A : KExpr) (B : KExpr) (a : KExpr) (b : KExpr), '
                'KernelAcceptsTcIn R tenv Bool.false G %s %s') % (N.HDR, e, fld)
        N.add_thm('accepts_tc_prod_proj_%d' % idx, ty_i,
                  'fun %s (cm : KCtorMeta) (hpm : Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) kcre_name_@@Prod.mk@@) (OptionType.some KCtorMeta cm)) '
                  '(hpn : Eq Nat (kctor_num_params cm) (Nat.succ (Nat.succ Nat.zero))) (us : ListType Level) (A : KExpr) (B : KExpr) (a : KExpr) (b : KExpr) => %s' % (N.HDR, proof))
    _ = ty


def proj_beta(idx, sub):
    head, args = spine(sub)
    A, B, a, b = args
    fld = a if idx == 0 else b
    return Conv(('proj', 'kcre_name_@@Prod@@', idx, sub), fld,
                '(accepts_tc_prod_proj_%d R tenv G cm hpm hpn %s %s %s %s %s)' % (idx, head[2], pr(A), pr(B), pr(a), pr(b)))


# ---------------------------------------------------------------- Bool
def gen_bool_not():
    op = 'Bool.not'
    CLOSURE[op] = [op]
    NEEDS[op] = {'bool'}
    b = bbody(op)

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(app(C(op), blit(v))), pr(blit('(Bool.not %s)' % v)))
    cases = []
    for v, k in (('Bool.false', FALSE), ('Bool.true', TRUE)):
        fr = bfront(op, b, [k])
        i1 = iota_bool(fr.rhs)
        i2 = betas(i1.rhs, 3)
        cases.append(retype_lhs(retype_rhs(chain([fr, i1, i2]), blit('(Bool.not %s)' % v)), app(C(op), blit(v))).proof)
    bregister(op, '(x : Bool)', Conv(app(C(op), blit('x')), blit('(Bool.not x)'), bool_case('x', mot, cases[0], cases[1])))


def gen_bool_bin(op, tails):
    """tails[(x, y)] -> function(term after iota+betas) -> convs to the result (both arguments split:
    a Bool literal on a variable is stuck under a binder)"""
    CLOSURE[op] = [op] + (['Bool.not'] if op == 'Bool.xor' else [])
    NEEDS[op] = {'bool'}
    b = bbody(op)
    K = {'Bool.false': FALSE, 'Bool.true': TRUE}

    def mot_y(xv):
        return lambda yv: 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(app(C(op), blit(xv), blit(yv))), pr(blit('(%s %s %s)' % (op, xv, yv))))

    def mot_x(xv):
        return 'forall (y : Bool), %s' % mot_y(xv)('y')

    def case(xv, yv):
        fr = bfront(op, b, [K[xv], K[yv]])
        i1 = iota_bool(fr.rhs)
        i2 = betas(i1.rhs, 3)
        tail = tails(xv, yv, i2.rhs)
        return retype_lhs(retype_rhs(chain([fr, i1, i2] + tail), blit('(%s %s %s)' % (op, xv, yv))), app(C(op), blit(xv), blit(yv))).proof

    def inner(xv):
        return 'fun (y : Bool) => %s' % bool_case('y', mot_y(xv), case(xv, 'Bool.false'), case(xv, 'Bool.true'))
    rec = '(%s y)' % bool_case('x', mot_x, inner('Bool.false'), inner('Bool.true'))
    bregister(op, '(x : Bool) (y : Bool)', Conv(app(C(op), blit('x'), blit('y')), blit('(%s x y)' % op), rec))


def gen_bools():
    gen_bool_not()
    K = {'Bool.false': FALSE, 'Bool.true': TRUE}

    def lit_(v):
        return K[v]

    def and_(xv, yv, t):
        assert eq(t, FALSE if xv == 'Bool.false' else lit_(yv)), pr(t)
        return []

    def or_(xv, yv, t):
        assert eq(t, lit_(yv) if xv == 'Bool.false' else TRUE), pr(t)
        return []

    def xor_(xv, yv, t):
        if xv == 'Bool.false':
            assert eq(t, lit_(yv)), pr(t)
            return []
        assert eq(t, app(C('Bool.not'), lit_(yv))), pr(t)
        return [retype_lhs(bcall('Bool.not', [yv], app(C('Bool.not'), blit(yv)), blit('(Bool.not %s)' % yv)), t)]
    gen_bool_bin('Bool.and', and_)
    gen_bool_bin('Bool.or', or_)
    gen_bool_bin('Bool.xor', xor_)


def gen_ofbool():
    op = 'Nat.ofBool'
    CLOSURE[op] = [op]
    NEEDS[op] = {'bool'}
    b = bbody(op)

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(app(C(op), blit(v))), pr(lit('(Nat.ofBool %s)' % v)))
    cases = []
    for v, k, tail in (('Bool.false', FALSE, lambda: [symm(lit_zero())]), ('Bool.true', TRUE, lambda: [N.one_conv()])):
        fr = bfront(op, b, [k])
        i1 = iota_bool(fr.rhs)
        i2 = betas(i1.rhs, 3)
        cases.append(retype_lhs(retype_rhs(chain([fr, i1, i2] + tail()), lit('(Nat.ofBool %s)' % v)), app(C(op), blit(v))).proof)
    bregister(op, '(x : Bool)', Conv(app(C(op), blit('x')), lit('(Nat.ofBool x)'), bool_case('x', mot, cases[0], cases[1])))


def gen_toboolpar():
    op = 'Nat.toBoolPar'
    CLOSURE[op] = [op]
    b = bbody(op)
    fr = bfront(op, b, [lit('n')])
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]

    def lhs(v):
        return N.natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(blit('(Nat.toBoolPar %s)' % v)))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    base_ = retype_rhs(chain([c1, c2, c3]), blit('(Nat.toBoolPar Nat.zero)'))
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ k)'), 'k')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    step = retype_rhs(chain([d1, d2, d3]), blit('(Nat.toBoolPar (Nat.succ k))'))
    rec = N.nat_rec_proof('n', mot, base_.proof, 'k', '_ih', step.proof)
    bregister(op, '(n : Nat)', trans(fr, Conv(fr.rhs, blit('(Nat.toBoolPar n)'), rec)))
