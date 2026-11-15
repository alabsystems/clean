"""Native-Nat folds, second part: Bool-valued comparisons, div / mod, the witness environment."""
# Part of the E4d native-fold generator (scripts/gen_accepts_tc_native_nat.py); outside the TCB --
# the Clean kernel re-checks every term it prints.
import kx
from nat_ops import *  # noqa: F401,F403 -- split for size; shares nat_ops' tables
import nat_ops as _N


def pr(t):
    return kx.pr(t)


# ---------------------------------------------------------------- Bool-valued comparisons (order_nat_cmp)
BOOL = C('Bool')
TRUE = C('Bool.true')
FALSE = C('Bool.false')
NATBOOL = lam(NAT, BOOL)
OUTER_M = lam(NAT, pi(NAT, BOOL))
CMP_SC = lam(NAT, lam(pi(NAT, BOOL), lam(NAT, natrec_app(NATBOOL, FALSE, lam(NAT, lam(BOOL, app(bv(3), bv(1)))), bv(0)))))
BODIES['Nat.beq'] = lam(NAT, lam(NAT, natrec_app(OUTER_M, lam(NAT, natrec_app(NATBOOL, TRUE, lam(NAT, lam(BOOL, FALSE)), bv(0))),
                                                  CMP_SC, bv(1), bv(0))))
BODIES['Nat.ble'] = lam(NAT, lam(NAT, natrec_app(OUTER_M, lam(NAT, TRUE), CMP_SC, bv(1), bv(0))))


def bool_lit_def():
    add_def('def accepts_tc_bool_lit (v : Bool) : KExpr := Bool.rec (fun (_ : Bool) => KExpr) '
            '(KExpr.const kcre_name_@@Bool.false@@ (ListType.nil Level)) (KExpr.const kcre_name_@@Bool.true@@ (ListType.nil Level)) v',
            'accepts_tc_bool_lit')


def gen_cmp(op):
    CLOSURE[op] = [op]
    b = hand_body_item(op)
    front = binop_front(op, b, 'a', 'b')
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    pre = 'accepts_tc_nat_%s' % short(op)
    name_param(pre + '_zcase', z, [])
    name_param(pre + '_scase', s, [])
    front = binop_front(op, b, 'a', 'b')

    def rec_at(x):
        return natrec_app(M, z, s, lit(x))

    def lhs(x, y):
        return app(rec_at(x), lit(y))

    def mot(v):
        return 'forall (b : Nat), KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v, 'b')), pr(blit('(%s %s b)' % (op, v))))

    # a = 0
    e = lhs('Nat.zero', 'b')
    c1 = major_to_ctor_zero(e)
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 4)
    inner = c3.rhs  # zero case applied to lit b
    if op == 'Nat.ble':
        assert eq(inner, TRUE), pr(inner)
        base0 = Conv(e, blit('(%s Nat.zero b)' % op),
                     'fun (b : Nat) => %s' % retype_rhs(chain([c1, c2, c3]), blit('(%s Nat.zero b)' % op)).proof)
        base_proof = base0.proof
    else:
        ih_, iargs = spine(inner)
        IM, IZ, IS = iargs[0], iargs[1], iargs[2]

        def imot(v):
            return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
                pr(natrec_app(IM, IZ, IS, lit(v))), pr(blit('(%s Nat.zero %s)' % (op, v))))
        f1 = major_to_ctor_zero(natrec_app(IM, IZ, IS, lit('Nat.zero')))
        f2 = iota_nat(f1.rhs)
        f3 = betas(f2.rhs, 3)
        assert eq(f3.rhs, TRUE), pr(f3.rhs)
        ib = retype_rhs(chain([f1, f2, f3]), blit('(%s Nat.zero Nat.zero)' % op))
        g1 = major_to_ctor_succ(natrec_app(IM, IZ, IS, lit('(Nat.succ j)')), 'j')
        g2 = iota_nat(g1.rhs)
        g3 = betas(g2.rhs, 6)
        assert eq(g3.rhs, FALSE), pr(g3.rhs)
        istep = retype_rhs(chain([g1, g2, g3]), blit('(%s Nat.zero (Nat.succ j))' % op))
        irec = nat_rec_proof('b', imot, ib.proof, 'j', '_jh', istep.proof)
        base_proof = 'fun (b : Nat) => %s' % trans(chain([c1, c2, c3]), Conv(inner, blit('(%s Nat.zero b)' % op), irec)).proof
    # a = succ k
    e = lhs('(Nat.succ k)', 'b')
    d1 = major_to_ctor_succ(e, 'k')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 7)
    inner = d3.rhs
    ih_, iargs = spine(inner)
    IM, IZ, IS = iargs[0], iargs[1], iargs[2]

    def smot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(natrec_app(IM, IZ, IS, lit(v))), pr(blit('(%s (Nat.succ k) %s)' % (op, v))))
    f1 = major_to_ctor_zero(natrec_app(IM, IZ, IS, lit('Nat.zero')))
    f2 = iota_nat(f1.rhs)
    f3 = betas(f2.rhs, 3)
    assert eq(f3.rhs, FALSE), pr(f3.rhs)
    sb = retype_rhs(chain([f1, f2, f3]), blit('(%s (Nat.succ k) Nat.zero)' % op))
    g1 = major_to_ctor_succ(natrec_app(IM, IZ, IS, lit('(Nat.succ j)')), 'j')
    g2 = iota_nat(g1.rhs)
    g3 = betas(g2.rhs, 6)
    assert eq(g3.rhs, lhs('k', 'j')), pr(g3.rhs)
    g4 = Conv(lhs('k', 'j'), blit('(%s k j)' % op), '(ih j)')
    sstep = retype_rhs(chain([g1, g2, g3, g4]), blit('(%s (Nat.succ k) (Nat.succ j))' % op))
    srec = nat_rec_proof('b', smot, sb.proof, 'j', '_jh', sstep.proof)
    step_proof = 'fun (b : Nat) => %s' % trans(chain([d1, d2, d3]), Conv(inner, blit('(%s (Nat.succ k) b)' % op), srec)).proof
    rec = '(%s b)' % nat_rec_proof('a', mot, base_proof, 'k', 'ih', step_proof)
    whole = trans(front, Conv(front.rhs, blit('(%s a b)' % op), rec))
    register(op, ['a', 'b'], whole)


def gen_beq():
    gen_cmp('Nat.beq')


def gen_ble():
    gen_cmp('Nat.ble')


# ---------------------------------------------------------------- Nat.blt (order_nat_cmp): a delta to Nat.ble
# `Nat.blt a b := Nat.ble (Nat.succ a) b`, so its fold is the already-proven `Nat.ble` fold at (succ a, b).
BODIES['Nat.blt'] = lam(NAT, lam(NAT, app(C('Nat.ble'), app(SUCC, bv(1)), bv(0))))


def gen_blt():
    CLOSURE['Nat.blt'] = ['Nat.blt']
    b = hand_body_item('Nat.blt')
    e0 = app(C('Nat.blt'), lit('a'), lit('b'))
    c1 = delta(e0, 'Nat.blt', ref(body_const('Nat.blt'), b), hyp('Nat.blt'))
    front = trans(c1, betas(c1.rhs, 2))
    # front.rhs = Nat.ble (Nat.succ (lit a)) (lit b); rewrite the first argument to a literal.
    step_succ = at_arg(front.rhs, 0, symm(lit_succ('a')))
    ble = Conv(step_succ.rhs, blit('(Nat.ble (Nat.succ a) b)'),
               '(kernel_accepts_tc_in_nat_ble_fold R tenv G (Nat.succ a) b %s hble)' % A_NATREC)
    whole = Conv(front.lhs, blit('(Nat.blt a b)'), trans(trans(front, step_succ), ble).proof)
    prem = (P_NATREC + ' ' + p_body('Nat.blt')
            + ' (hble : Eq (OptionType KExpr) (kdef_value_at (red_def R) kcre_name_@@Nat.ble@@ '
              '(ListType.nil Level)) (OptionType.some KExpr accepts_tc_nat_ble_body))')
    ty = 'forall %s (a : Nat) (b : Nat) %s, %s' % (HDR, prem, whole.ty())
    add_thm('kernel_accepts_tc_in_nat_blt_fold', ty,
            'fun %s (a : Nat) (b : Nat) %s => %s' % (HDR, prem, whole.proof))


# ---------------------------------------------------------------- fuel-bounded div / mod (init_nat)
SUB = C('Nat.sub')
NN2 = pi(NAT, pi(NAT, NAT))
DM = lam(NAT, NN2)
DIV_X = app(SUCC, app(bv(2), app(SUB, bv(1), bv(0)), bv(0)))
MOD_X = app(bv(2), app(SUB, bv(1), bv(0)), bv(0))
YZERO = lam(NAT, lam(NAT, ZERO))
BODIES['Nat.divCore'] = lam(NAT, lam(NAT, lam(NAT, natrec_app(
    DM, lam(NAT, lam(NAT, ZERO)),
    lam(NAT, lam(NN2, lam(NAT, lam(NAT, natrec_app(NATNAT, DIV_X, YZERO, app(SUB, bv(0), bv(1))))))),
    bv(2), bv(1), bv(0)))))
BODIES['Nat.modCore'] = lam(NAT, lam(NAT, lam(NAT, natrec_app(
    DM, lam(NAT, lam(NAT, bv(1))),
    lam(NAT, lam(NN2, lam(NAT, lam(NAT, natrec_app(NATNAT, MOD_X, lam(NAT, lam(NAT, bv(3))), app(SUB, bv(0), bv(1))))))),
    bv(2), bv(1), bv(0)))))
BODIES['Nat.div'] = lam(NAT, lam(NAT, natrec_app(NATNAT, ZERO, lam(NAT, lam(NAT, app(C('Nat.divCore'), bv(3), bv(3), app(SUCC, bv(1))))), bv(0))))
BODIES['Nat.mod'] = lam(NAT, lam(NAT, app(C('Nat.modCore'), bv(1), bv(1), bv(0))))


def gen_select(name, ycase, yval_payload, params):
    """Nat.rec (fun _ => Nat) (lit xv) Y (lit k) == lit (Nat.rec (fun _ => Nat) xv (fun _ _ => c) k)"""
    def lhs(v):
        return natrec_app(NATNAT, lit('xv'), ycase, lit(v))

    def meta(v):
        return '(Nat.rec (fun (_ : Nat) => Nat) xv (fun (_ : Nat) (_ : Nat) => %s) %s)' % (yval_payload, v)

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(lit(meta(v))))
    c1 = major_to_ctor_zero(lhs('Nat.zero'))
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    assert eq(c3.rhs, lit('xv')), pr(c3.rhs)
    base = retype_rhs(chain([c1, c2, c3]), lit(meta('Nat.zero')))
    d1 = major_to_ctor_succ(lhs('(Nat.succ j)'), 'j')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    tail = [symm(lit_zero())] if eq(d3.rhs, ZERO) else []
    if not tail:
        assert eq(d3.rhs, lit(yval_payload)), pr(d3.rhs)
    step = retype_rhs(chain([d1, d2, d3] + tail), lit(meta('(Nat.succ j)')))
    rec = nat_rec_proof('k', mot, base.proof, 'j', '_jh', step.proof)
    binders = ' '.join('(%s : Nat)' % p for p in params + ['k'])
    ty = 'forall %s %s %s, %s' % (HDR, binders, P_NATREC, mot('k'))
    add_thm(name, ty, 'fun %s %s %s => %s' % (HDR, binders, P_NATREC, rec))
    return lambda xv, k, *extra: Conv(
        natrec_app(NATNAT, lit(xv), ycase if not extra else inst_payload(ycase, extra), lit(k)),
        lit('(Nat.rec (fun (_ : Nat) => Nat) %s (fun (_ : Nat) (_ : Nat) => %s) %s)' % (
            xv, yval_payload if not extra else extra[0], k)),
        '(%s R tenv G %s %s %s %s)' % (name, ' '.join(extra), xv, k, A_NATREC) if extra else
        '(%s R tenv G %s %s %s)' % (name, xv, k, A_NATREC))


def inst_payload(t, extra):
    """replace lit('c') in ycase by lit(extra[0])"""
    tag = t[0]
    if tag == 'lit' and t[1] == 'c':
        return lit(extra[0])
    if tag in ('app', 'lam', 'pi'):
        return (tag, inst_payload(t[1], extra), inst_payload(t[2], extra))
    return t


SELECT_ZERO = None
SELECT_LIT = None


def gen_selects():
    global SELECT_ZERO, SELECT_LIT
    SELECT_ZERO = gen_select('accepts_tc_nat_rec_select_zero', YZERO, 'Nat.zero', ['xv'])
    SELECT_LIT = gen_select('accepts_tc_nat_rec_select_lit', lam(NAT, lam(NAT, lit('c'))), 'c', ['c', 'xv'])


def gen_fuel(op, xform, sel):
    """divCore / modCore: induction on the fuel, generalised over the two arguments"""
    b = hand_body_item(op)
    e0 = app(C(op), lit('f'), lit('a'), lit('n'))
    c1 = delta(e0, op, ref(body_const(op), b), hyp(op))
    front = trans(c1, betas(c1.rhs, 3))
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    pre = 'accepts_tc_nat_%s' % short(op)
    name_param(pre + '_zcase', z, [])
    name_param(pre + '_scase', s, [])
    front = trans(c1, betas(c1.rhs, 3))

    def lhs(v, x, y):
        return natrec_app(M, z, s, lit(v), lit(x), lit(y))

    def mot(v):
        return 'forall (a : Nat) (n : Nat), KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(lhs(v, 'a', 'n')), pr(lit('(%s %s a n)' % (op, v))))
    e = lhs('Nat.zero', 'a', 'n')
    b1 = major_to_ctor_zero(e)
    b2 = iota_nat(b1.rhs)
    b3 = betas(b2.rhs, 5)
    tail = [symm(lit_zero())] if eq(b3.rhs, ZERO) else []
    if not tail:
        assert eq(b3.rhs, lit('a')), pr(b3.rhs)
    base = 'fun (a : Nat) (n : Nat) => %s' % retype_rhs(chain([b1, b2, b3] + tail), lit('(%s Nat.zero a n)' % op)).proof
    e = lhs('(Nat.succ g)', 'a', 'n')
    d1 = major_to_ctor_succ(e, 'g')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 8)
    inner = d3.rhs  # Nat.rec NATNAT X Y (sub n a)
    ih_, iargs = spine(inner)
    X, Y, MAJ = iargs[1], iargs[2], iargs[3]
    assert eq(MAJ, app(SUB, lit('n'), lit('a'))), pr(MAJ)
    # X: [succ] (rec_g (sub a n) n)
    rec_call = X[2] if xform == 'div' else X
    rhead, rargs = spine(rec_call)
    assert eq(rargs[4], app(SUB, lit('a'), lit('n'))), pr(rargs[4])
    x1 = at_arg(rec_call, 4, call('Nat.sub', 'a', 'n'))
    x2 = Conv(x1.rhs, lit('(%s g (Nat.sub a n) n)' % op), '(ih (Nat.sub a n) n)')
    assert eq(x1.rhs, lhs('g', '(Nat.sub a n)', 'n')), pr(x1.rhs)
    if xform == 'div':
        xconv = chain([app_r(SUCC, chain([x1, x2])), symm(lit_succ('(%s g (Nat.sub a n) n)' % op))])
        xv = '(Nat.succ (%s g (Nat.sub a n) n))' % op
    else:
        xconv = chain([x1, x2])
        xv = '(%s g (Nat.sub a n) n)' % op
    s1 = at_arg(inner, 1, xconv)
    s2 = at_arg(s1.rhs, 3, call('Nat.sub', 'n', 'a'))
    if xform == 'div':
        s3 = SELECT_ZERO(xv, '(Nat.sub n a)')
    else:
        s3 = SELECT_LIT(xv, '(Nat.sub n a)', 'a')
    step = 'fun (a : Nat) (n : Nat) => %s' % retype_rhs(chain([d1, d2, d3, s1, s2, s3]), lit('(%s (Nat.succ g) a n)' % op)).proof
    rec = '(%s a n)' % nat_rec_proof('f', mot, base, 'g', 'ih', step)
    register(op, ['f', 'a', 'n'], trans(front, Conv(front.rhs, lit('(%s f a n)' % op), rec)))


def gen_divmod():
    CLOSURE['Nat.divCore'] = ['Nat.divCore', 'Nat.sub', 'Nat.pred']
    CLOSURE['Nat.modCore'] = ['Nat.modCore', 'Nat.sub', 'Nat.pred']
    CLOSURE['Nat.div'] = ['Nat.div', 'Nat.divCore', 'Nat.sub', 'Nat.pred']
    CLOSURE['Nat.mod'] = ['Nat.mod', 'Nat.modCore', 'Nat.sub', 'Nat.pred']
    gen_selects()
    gen_fuel('Nat.divCore', 'div', SELECT_ZERO)
    gen_fuel('Nat.modCore', 'mod', SELECT_LIT)
    # div
    b = hand_body_item('Nat.div')
    front = binop_front('Nat.div', b, 'a', 'n')
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    name_param('accepts_tc_nat_div_scase', s, ['a'])
    front = binop_front('Nat.div', b, 'a', 'n')

    def lhs(v):
        return natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(lit('(Nat.div a %s)' % v)))
    c1 = major_to_ctor_zero(lhs('Nat.zero'))
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    base = retype_rhs(chain([c1, c2, c3, symm(lit_zero())]), lit('(Nat.div a Nat.zero)'))
    d1 = major_to_ctor_succ(lhs('(Nat.succ j)'), 'j')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    assert eq(d3.rhs, app(C('Nat.divCore'), lit('a'), lit('a'), app(SUCC, lit('j')))), pr(d3.rhs)
    d4 = at_arg(d3.rhs, 2, symm(lit_succ('j')))
    d5 = call('Nat.divCore', 'a', 'a', '(Nat.succ j)')
    step = retype_rhs(chain([d1, d2, d3, d4, d5]), lit('(Nat.div a (Nat.succ j))'))
    rec = nat_rec_proof('n', mot, base.proof, 'j', '_jh', step.proof)
    register('Nat.div', ['a', 'n'], trans(front, Conv(front.rhs, lit('(Nat.div a n)'), rec)))
    # mod
    b = hand_body_item('Nat.mod')
    front = binop_front('Nat.mod', b, 'a', 'n')
    assert eq(front.rhs, app(C('Nat.modCore'), lit('a'), lit('a'), lit('n'))), pr(front.rhs)
    whole = retype_rhs(trans(front, call('Nat.modCore', 'a', 'a', 'n')), lit('(Nat.mod a n)'))
    register('Nat.mod', ['a', 'n'], whole)


# ---------------------------------------------------------------- the witness environment and instances
TYPES = {
    'Nat.mul': pi(NAT, pi(NAT, NAT)), 'Nat.pow': pi(NAT, pi(NAT, NAT)), 'Nat.shiftLeft': pi(NAT, pi(NAT, NAT)),
    'Nat.beq': pi(NAT, pi(NAT, C('Bool'))), 'Nat.ble': pi(NAT, pi(NAT, C('Bool'))),
    'Nat.divCore': pi(NAT, pi(NAT, pi(NAT, NAT))), 'Nat.modCore': pi(NAT, pi(NAT, pi(NAT, NAT))),
    'Nat.div': pi(NAT, pi(NAT, NAT)), 'Nat.mod': pi(NAT, pi(NAT, NAT)),
}
REFLECTED_IN_CORE = ['Nat.pred', 'Nat.add', 'Nat.sub']


def nat_term(n):
    t = 'Nat.zero'
    for _ in range(n):
        t = '(Nat.succ %s)' % t
    return t


def gen_env_and_instances():
    defenv = '(red_def kernel_core_red_env)'
    for op in [o for o in ORDER if o in TYPES and o in CLOSURE]:
        defenv = '(DefEnv.addDef %s kcre_name_@@%s@@ (KDefSig.mk (KConstSig.mk (ListType.nil Name) %s) %s))' % (
            defenv, op, pr(TYPES[op]), body_const(op))
    add_def('def accepts_tc_nat_fold_env : RedEnv := RedEnv.mk (red_rec kernel_core_red_env) %s (red_ind_ctor kernel_core_red_env)' % defenv,
            'accepts_tc_nat_fold_env')
    # the reflected core holds the specification's own three: its entries ARE the canonical bodies
    for op in REFLECTED_IN_CORE:
        add_thm('accepts_tc_nat_%s_body_reflected' % short(op),
                'Eq (OptionType KExpr) (kdef_value_at (red_def kernel_core_red_env) kcre_name_@@%s@@ (ListType.nil Level)) (OptionType.some KExpr %s)' % (op, body_const(op)),
                'Eq.refl (OptionType KExpr) (OptionType.some KExpr %s)' % body_const(op))
    env = 'accepts_tc_nat_fold_env'
    refl_meta = '(Eq.refl (OptionType RecMeta) (OptionType.some RecMeta kcre_rec_meta_@@Nat.rec@@))'
    refl_z = '(Eq.refl (OptionType RecRule) (OptionType.some RecRule accepts_tc_nat_rec_zero_rule))'
    refl_s = '(Eq.refl (OptionType RecRule) (OptionType.some RecRule accepts_tc_nat_rec_succ_rule))'
    instances = [('Nat.add', (2, 3)), ('Nat.sub', (5, 2)), ('Nat.mul', (2, 3)), ('Nat.pow', (2, 3)),
                 ('Nat.shiftLeft', (3, 2)), ('Nat.beq', (2, 2)), ('Nat.ble', (3, 2)), ('Nat.div', (7, 2)),
                 ('Nat.mod', (7, 3)), ('Nat.pred', (4,))]
    for op, args in instances:
        prems = ' '.join([refl_meta, refl_z, refl_s] + [
            '(Eq.refl (OptionType KExpr) (OptionType.some KExpr %s))' % body_const(o) for o in closure_sorted(op)])
        ns = [nat_term(a) for a in args]
        lhs = app(C(op), *[lit(n) for n in ns])
        rhs_payload = '(%s %s)' % (op, ' '.join(ns))
        rhs = blit(rhs_payload) if op in ('Nat.beq', 'Nat.ble') else lit(rhs_payload)
        ty = 'forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn %s tenv Bool.false G %s %s' % (env, pr(lhs), pr(rhs))
        add_thm('accepts_tc_nat_%s_instance' % short(op), ty,
                'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => %s %s tenv G %s %s' % (lemma_name(op), env, ' '.join(ns), prems))
        sty = 'forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), TypingTcIn %s tenv Bool.false G %s %s' % (env, pr(lhs), pr(rhs))
        add_thm('accepts_tc_nat_%s_instance_sound' % short(op), sty,
                'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => kernel_accepts_tc_in_sound %s tenv Bool.false G %s %s (accepts_tc_nat_%s_instance tenv G)' % (
                    env, pr(lhs), pr(rhs), short(op)))


def main_items():
    base_items()
    gen_succ()
    gen_pred()
    gen_add()
    gen_sub()
    gen_mul()
    gen_pow()
    gen_shl()
    bool_lit_def()
    gen_beq()
    gen_ble()
    gen_blt()
    gen_divmod()
    gen_env_and_instances()
