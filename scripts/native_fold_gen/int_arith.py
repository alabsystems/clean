"""Native Int folds, second part: Int.add / Int.mul / Int.sub and the predecessor fold."""
# Part of the E4d native-fold generator (scripts/gen_accepts_tc_native_nat.py); outside the TCB --
# the Clean kernel re-checks every term it prints.
import kx
import nat_ops as N
from int_ops import *  # noqa: F401,F403 -- split for size; shares int_ops' tables
import int_ops as _I


def pr(t):
    return kx.pr(t)


# ---------------------------------------------------------------- Int.add / Int.mul: four constructor cases
def gen_binop(op, cases):
    """cases[(cx, cy)] = function(conv_so_far_rhs) -> list of tail convs ending at the result"""
    b = ibody(op)

    def mot_y(xv):
        return lambda yv: 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(app(C(op), ilit(xv), ilit(yv))), pr(ilit('(%s %s %s)' % (op, xv, yv))))

    def mot_x(xv):
        return 'forall (y : Int), %s' % mot_y(xv)('y')

    pre = 'accepts_tc_%s' % op.replace('.', '_').lower()
    fr0 = front(op, b, [ctor_lit('ofNat', 'a'), ctor_lit('ofNat', 'b')])
    h0, a0 = spine(fr0.rhs)
    N.name_param(pre + '_motive', a0[0], [])
    N.name_param(pre + '_ofnat_case', a0[1], [])
    N.name_param(pre + '_negsucc_case', a0[2], [])
    for cx in ('ofNat', 'negSucc'):
        fr1 = front(op, b, [ctor_lit(cx, 'a'), ctor_lit('ofNat', 'b')])
        j1 = iota_int(fr1.rhs)
        j2 = betas(j1.rhs, 6)
        h1, a1 = spine(j2.rhs)
        N.name_param('%s_%s_inner_ofnat' % (pre, cx.lower()), a1[1], ['a'])
        N.name_param('%s_%s_inner_negsucc' % (pre, cx.lower()), a1[2], ['a'])

    def case_proof(cx, a, cy, bb):
        xv = '(Int.%s %s)' % (cx, a)
        yv = '(Int.%s %s)' % (cy, bb)
        fr = front(op, b, [ctor_lit(cx, a), ctor_lit(cy, bb)])
        i1 = iota_int(fr.rhs)
        i2 = betas(i1.rhs, 6)
        i3 = iota_int(i2.rhs)
        i4 = betas(i3.rhs, 5)
        tail = cases[(cx, cy)](i4.rhs, a, bb)
        c = retype_rhs(chain([fr, i1, i2, i3, i4] + tail), ilit('(%s %s %s)' % (op, xv, yv)))
        return retype_lhs(c, app(C(op), ilit(xv), ilit(yv))).proof

    def inner(cx, a):
        xv = '(Int.%s %s)' % (cx, a)
        return 'fun (y : Int) => %s' % int_rec_proof('y', mot_y(xv), 'b', case_proof(cx, a, 'ofNat', 'b'),
                                                       'b', case_proof(cx, a, 'negSucc', 'b'))
    rec = '(%s y)' % int_rec_proof('x', mot_x, 'a', inner('ofNat', 'a'), 'a', inner('negSucc', 'a'))
    whole = Conv(app(C(op), ilit('x'), ilit('y')), ilit('(%s x y)' % op), rec)
    iregister(op, '(x : Int) (y : Int)', whole)


def gen_add():
    op = 'Int.add'
    INT_CLOSURE[op] = [op, 'Int.subNatNat']
    NAT_NEEDS[op] = ['Nat.add']
    ADD = C('Nat.add')
    SNN = C('Int.subNatNat')

    def oo(t, a, bb):
        assert eq(t, app(OFNAT, app(ADD, lit(a), lit(bb)))), pr(t)
        return [app_r(OFNAT, N.call('Nat.add', a, bb))]

    def on(t, a, bb):
        assert eq(t, app(SNN, lit(a), app(N.SUCC, lit(bb)))), pr(t)
        return [at_arg(t, 1, symm(lit_succ(bb))),
                icall('Int.subNatNat', [a, '(Nat.succ %s)' % bb], 'nn', ilit('(Int.subNatNat %s (Nat.succ %s))' % (a, bb)))]

    def no(t, a, bb):
        assert eq(t, app(SNN, lit(bb), app(N.SUCC, lit(a)))), pr(t)
        return [at_arg(t, 1, symm(lit_succ(a))),
                icall('Int.subNatNat', [bb, '(Nat.succ %s)' % a], 'nn', ilit('(Int.subNatNat %s (Nat.succ %s))' % (bb, a)))]

    def nn(t, a, bb):
        assert eq(t, app(NEGSUCC, app(N.SUCC, app(ADD, lit(a), lit(bb))))), pr(t)
        return [app_r(NEGSUCC, app_r(N.SUCC, N.call('Nat.add', a, bb))),
                app_r(NEGSUCC, symm(lit_succ('(Nat.add %s %s)' % (a, bb))))]
    gen_binop(op, {('ofNat', 'ofNat'): oo, ('ofNat', 'negSucc'): on, ('negSucc', 'ofNat'): no, ('negSucc', 'negSucc'): nn})


def gen_mul():
    op = 'Int.mul'
    INT_CLOSURE[op] = [op, 'Int.negOfNat']
    NAT_NEEDS[op] = ['Nat.mul', 'Nat.add']
    MUL = C('Nat.mul')
    NEG = C('Int.negOfNat')

    def nat_arg(t):
        """rewrite succ (lit x) arguments of a Nat.mul to literals, then fold the product"""
        return t

    def mul_fold(t, x_is_succ, xa, y_is_succ, yb):
        convs = []
        cur = t
        xp = '(Nat.succ %s)' % xa if x_is_succ else xa
        yp = '(Nat.succ %s)' % yb if y_is_succ else yb
        if x_is_succ:
            c = at_arg(cur, 0, symm(lit_succ(xa)))
            convs.append(c)
            cur = c.rhs
        if y_is_succ:
            c = at_arg(cur, 1, symm(lit_succ(yb)))
            convs.append(c)
            cur = c.rhs
        convs.append(N.call('Nat.mul', xp, yp))
        return convs, '(Nat.mul %s %s)' % (xp, yp)

    def oo(t, a, bb):
        assert eq(t, app(OFNAT, app(MUL, lit(a), lit(bb)))), pr(t)
        convs, v = mul_fold(t[2], False, a, False, bb)
        return [app_r(OFNAT, chain(convs))]

    def on(t, a, bb):
        assert eq(t, app(NEG, app(MUL, lit(a), app(N.SUCC, lit(bb))))), pr(t)
        convs, v = mul_fold(t[2], False, a, True, bb)
        return [app_r(NEG, chain(convs)), icall('Int.negOfNat', [v], 'n', ilit('(Int.negOfNat %s)' % v))]

    def no(t, a, bb):
        assert eq(t, app(NEG, app(MUL, app(N.SUCC, lit(a)), lit(bb)))), pr(t)
        convs, v = mul_fold(t[2], True, a, False, bb)
        return [app_r(NEG, chain(convs)), icall('Int.negOfNat', [v], 'n', ilit('(Int.negOfNat %s)' % v))]

    def nn(t, a, bb):
        assert eq(t, app(OFNAT, app(MUL, app(N.SUCC, lit(a)), app(N.SUCC, lit(bb))))), pr(t)
        convs, v = mul_fold(t[2], True, a, True, bb)
        return [app_r(OFNAT, chain(convs))]
    gen_binop(op, {('ofNat', 'ofNat'): oo, ('ofNat', 'negSucc'): on, ('negSucc', 'ofNat'): no, ('negSucc', 'negSucc'): nn})


def gen_sub():
    """Int.sub x y := Int.add x (Int.neg y): split both (an int literal on a variable is stuck under a binder)"""
    op = 'Int.sub'
    INT_CLOSURE[op] = [op, 'Int.add', 'Int.neg', 'Int.subNatNat']
    NAT_NEEDS[op] = ['Nat.add']
    b = ibody(op)

    def mot_y(xv):
        return lambda yv: 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (
            pr(app(C(op), ilit(xv), ilit(yv))), pr(ilit('(Int.sub %s %s)' % (xv, yv))))

    def mot_x(xv):
        return 'forall (y : Int), %s' % mot_y(xv)('y')

    def case_proof(cx, a, cy, bb):
        xv = '(Int.%s %s)' % (cx, a)
        yv = '(Int.%s %s)' % (cy, bb)
        fr = front(op, b, [ctor_lit(cx, a), ctor_lit(cy, bb)])
        assert eq(fr.rhs, app(C('Int.add'), ctor_lit(cx, a), app(C('Int.neg'), ctor_lit(cy, bb)))), pr(fr.rhs)
        c1 = at_arg(fr.rhs, 1, retype_lhs(icall('Int.neg', [yv], 'i', ilit('(Int.neg %s)' % yv)), app(C('Int.neg'), ctor_lit(cy, bb))))
        c2 = retype_lhs(icall('Int.add', [xv, '(Int.neg %s)' % yv], 'ii', ilit('(Int.add %s (Int.neg %s))' % (xv, yv))),
                        c1.rhs)
        c = retype_rhs(chain([fr, c1, c2]), ilit('(Int.sub %s %s)' % (xv, yv)))
        return retype_lhs(c, app(C(op), ilit(xv), ilit(yv))).proof

    def inner(cx, a):
        xv = '(Int.%s %s)' % (cx, a)
        return 'fun (y : Int) => %s' % int_rec_proof('y', mot_y(xv), 'b', case_proof(cx, a, 'ofNat', 'b'),
                                                       'b', case_proof(cx, a, 'negSucc', 'b'))
    rec = '(%s y)' % int_rec_proof('x', mot_x, 'a', inner('ofNat', 'a'), 'a', inner('negSucc', 'a'))
    iregister(op, '(x : Int) (y : Int)', Conv(app(C(op), ilit('x'), ilit('y')), ilit('(Int.sub x y)'), rec))


def gen_pred_fold():
    """reduce_int_pred_fold: Nat.rec (fun _ => Int) z <the pinned predecessor step> count (z split first)"""
    M = lam(NAT, INT)

    def meta(zv, v):
        return ('(@Nat.rec (fun (_ : Nat) => Int) %s (fun (_ : Nat) (ih : Int) => %s) %s)' % (zv, pred_step_meta('ih'), v))

    def lhs(zt, v):
        return N.natrec_app(M, zt, PRED_STEP, lit(v))

    def zcase(cz, a):
        zv = '(Int.%s %s)' % (cz, a)
        zt = ctor_lit(cz, a)

        def mot(v):
            return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(ilit(zv), v)), pr(ilit(meta(zv, v))))
        c1 = N.major_to_ctor_zero(lhs(zt, 'Nat.zero'))
        c2 = N.iota_nat(c1.rhs)
        c3 = betas(c2.rhs, 3)
        base_ = retype_lhs(retype_rhs(chain([c1, c2, c3]), ilit(meta(zv, 'Nat.zero'))), lhs(ilit(zv), 'Nat.zero'))
        d1 = N.major_to_ctor_succ(lhs(zt, '(Nat.succ k)'), 'k')
        d2 = N.iota_nat(d1.rhs)
        d3 = betas(d2.rhs, 6)
        d4 = at_arg(d3.rhs, 3, retype_lhs(Conv(lhs(ilit(zv), 'k'), ilit(meta(zv, 'k')), 'ih'), lhs(zt, 'k')))
        d5 = _I.PRED_SELECT(meta(zv, 'k'))
        step = retype_lhs(retype_rhs(chain([d1, d2, d3, d4, d5]), ilit(meta(zv, '(Nat.succ k)'))), lhs(ilit(zv), '(Nat.succ k)'))
        return N.nat_rec_proof('c', mot, base_.proof, 'k', 'ih', step.proof)

    def zmot(zv):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(ilit(zv), 'c')), pr(ilit(meta(zv, 'c'))))
    rec = int_rec_proof('z', zmot, 'a', zcase('ofNat', 'a'), 'a', zcase('negSucc', 'a'))
    ty = 'forall %s (z : Int) (c : Nat) %s %s, %s' % (N.HDR, N.P_NATREC, P_INTREC, zmot('z'))
    N.add_thm('kernel_accepts_tc_in_int_pred_fold', ty, 'fun %s (z : Int) (c : Nat) %s %s => %s' % (N.HDR, N.P_NATREC, P_INTREC, rec))


def int_items():
    base()
    gen_negofnat()
    gen_neg()
    gen_subnatnat()
    gen_add()
    gen_mul()
    gen_sub()
    gen_tonat()
    gen_pred_fold()
