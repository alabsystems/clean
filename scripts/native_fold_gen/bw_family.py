"""Bitwise native folds, second part: pairs, div2, shifts, testBit and the bitwise family."""
# Part of the E4d native-fold generator (scripts/gen_accepts_tc_native_nat.py); outside the TCB --
# the Clean kernel re-checks every term it prints.
import kx
import nat_ops as N
from bw_ops import *  # noqa: F401,F403 -- split for size; shares bw_ops' tables


def pr(t):
    return kx.pr(t)


# ---------------------------------------------------------------- pairs and projections
def gen_fst_snd():
    for op, idx in (('Prod.fst', 0), ('Prod.snd', 1)):
        CLOSURE[op] = [op]
        NEEDS[op] = {'prod'}
        b = bbody(op)
        fr = bfront(op, b, [NAT, NAT, plit('p')])
        sub = pair(lit('(Prod.fst Nat Nat p)'), lit('(Prod.snd Nat Nat p)'))
        assert fr.rhs[0] == 'proj', pr(fr.rhs)
        pb = proj_beta(idx, sub)
        pb = retype_lhs(pb, fr.rhs)
        whole = trans(fr, pb)
        whole = retype_rhs(whole, lit('(%s Nat Nat p)' % op))
        bregister(op, '(p : Prod Nat Nat)', whole)


def call_fst(idx, x):
    op = 'Prod.fst' if idx == 0 else 'Prod.snd'
    return bcall(op, [x], app(C(op, LV00), NAT, NAT, plit(x)), lit('(%s Nat Nat %s)' % (op, x)))


def gen_div2pair():
    op = 'Nat.div2Pair'
    CLOSURE[op] = [op, 'Prod.fst', 'Prod.snd', 'Nat.add', 'Nat.sub', 'Nat.pred']
    b = bbody(op)
    fr = bfront(op, b, [lit('n')])
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]
    N.name_param('accepts_tc_nat_div2pair_scase', s, [])

    def lhs(v):
        return N.natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(plit('(Nat.div2Pair %s)' % v)))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    assert eq(c3.rhs, pair(ZERO, ZERO)), pr(c3.rhs)
    c4 = at_arg(c3.rhs, 2, symm(lit_zero()))
    c5 = at_arg(c4.rhs, 3, symm(lit_zero()))
    base_ = retype_rhs(chain([c1, c2, c3, c4, c5]), plit('(Nat.div2Pair Nat.zero)'))
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ k)'), 'k')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    X = '(Nat.div2Pair k)'
    rec_k = lhs('k')
    ih = Conv(rec_k, plit(X), 'ih')
    t = d3.rhs
    fx, sx = '(Prod.fst Nat Nat %s)' % X, '(Prod.snd Nat Nat %s)' % X
    convs = []
    # first field: add (fst REC) (snd REC)
    for path in ([2, 0, 2], [2, 1, 2], [3, 1, 2]):
        c = at_path(t, path, ih)
        convs.append(c)
        t = c.rhs
    for path, idx in (([2, 0], 0), ([2, 1], 1), ([3, 1], 1)):
        c = at_path(t, path, call_fst(idx, X))
        convs.append(c)
        t = c.rhs
    c = at_path(t, [2], N.call('Nat.add', fx, sx))
    convs.append(c)
    t = c.rhs
    c = at_path(t, [3, 0], N.one_conv())
    convs.append(c)
    t = c.rhs
    c = at_path(t, [3], N.call('Nat.sub', '(Nat.succ Nat.zero)', sx))
    convs.append(c)
    step = retype_rhs(chain([d1, d2, d3] + convs), plit('(Nat.div2Pair (Nat.succ k))'))
    rec = N.nat_rec_proof('n', mot, base_.proof, 'k', 'ih', step.proof)
    bregister(op, '(n : Nat)', trans(fr, Conv(fr.rhs, plit('(Nat.div2Pair n)'), rec)))


def gen_div2(op, idx):
    CLOSURE[op] = [op, 'Nat.div2Pair', 'Prod.fst' if idx == 0 else 'Prod.snd']
    b = bbody(op)
    fr = bfront(op, b, [lit('n')])
    c1 = at_path(fr.rhs, [2], bcall('Nat.div2Pair', ['n'], app(C('Nat.div2Pair'), lit('n')), plit('(Nat.div2Pair n)')))
    c2 = call_fst(idx, '(Nat.div2Pair n)')
    bregister(op, '(n : Nat)', retype_rhs(chain([fr, c1, c2]), lit('(%s n)' % op)))


def gen_iterdiv2():
    op = 'Nat.iterDiv2'
    CLOSURE[op] = [op, 'Nat.div2']
    b = bbody(op)
    e0 = app(C(op), lit('k'), lit('m'))
    c1 = delta(e0, op, b, bhyp(op))
    fr = trans(c1, betas(c1.rhs, 1))
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]
    N.name_param('accepts_tc_nat_iterdiv2_scase', s, [])

    def lhs(v, x):
        return N.natrec_app(M, z, s, lit(v), lit(x))

    def mot(v):
        return 'forall (m : Nat), KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v, 'm')), pr(lit('(Nat.iterDiv2 %s m)' % v)))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero', 'm'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 4)
    assert eq(c3.rhs, lit('m')), pr(c3.rhs)
    base_ = 'fun (m : Nat) => %s' % retype_rhs(chain([c1, c2, c3]), lit('(Nat.iterDiv2 Nat.zero m)')).proof
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ g)', 'm'), 'g')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 7)
    assert eq(d3.rhs, app(N.natrec_app(M, z, s, lit('g')), app(C('Nat.div2'), lit('m')))), pr(d3.rhs)
    d4 = at_arg(d3.rhs, 4, bcall('Nat.div2', ['m'], app(C('Nat.div2'), lit('m')), lit('(Nat.div2 m)')))
    d5 = Conv(lhs('g', '(Nat.div2 m)'), lit('(Nat.iterDiv2 g (Nat.div2 m))'), '(ih (Nat.div2 m))')
    step = 'fun (m : Nat) => %s' % retype_rhs(chain([d1, d2, d3, d4, d5]), lit('(Nat.iterDiv2 (Nat.succ g) m)')).proof
    rec = '(%s m)' % N.nat_rec_proof('k', mot, base_, 'g', 'ih', step)
    bregister(op, '(k : Nat) (m : Nat)', trans(fr, Conv(fr.rhs, lit('(Nat.iterDiv2 k m)'), rec)))


def iter_call(k, m):
    return bcall('Nat.iterDiv2', [k, m], app(C('Nat.iterDiv2'), lit(k), lit(m)), lit('(Nat.iterDiv2 %s %s)' % (k, m)))


def gen_shiftright():
    op = 'Nat.shiftRight'
    CLOSURE[op] = [op, 'Nat.iterDiv2']
    b = bbody(op)
    fr = bfront(op, b, [lit('a'), lit('b')])
    bregister(op, '(a : Nat) (b : Nat)', retype_rhs(chain([fr, iter_call('b', 'a')]), lit('(Nat.shiftRight a b)')))


def gen_testbit():
    op = 'Nat.testBit'
    CLOSURE[op] = [op, 'Nat.toBoolPar', 'Nat.div2Par', 'Nat.iterDiv2']
    b = bbody(op)
    fr = bfront(op, b, [lit('m'), lit('i')])
    c1 = at_path(fr.rhs, [0, 0], iter_call('i', 'm'))
    v = '(Nat.iterDiv2 i m)'
    c2 = at_path(c1.rhs, [0], bcall('Nat.div2Par', [v], app(C('Nat.div2Par'), lit(v)), lit('(Nat.div2Par %s)' % v)))
    w = '(Nat.div2Par %s)' % v
    c3 = bcall('Nat.toBoolPar', [w], app(C('Nat.toBoolPar'), lit(w)), blit('(Nat.toBoolPar %s)' % w))
    bregister(op, '(m : Nat) (i : Nat)', retype_rhs(chain([fr, c1, c2, c3]), blit('(Nat.testBit m i)')))


def testbit_call(m):
    return bcall('Nat.testBit', [m, 'Nat.zero'], app(C('Nat.testBit'), lit(m), lit('Nat.zero')), blit('(Nat.testBit %s Nat.zero)' % m))


def gen_bitwiseaux(fop):
    op = 'Nat.bitwiseAux'
    key = 'Nat.bitwiseAux'  # one body, three lemmas
    CLOSURE[key] = [key, 'Nat.div2', 'Nat.testBit', 'Nat.ofBool', fop, 'Nat.add']
    NEEDS[key] = {'bool'}
    b = BODY_REFS.get(key) or bbody(key)
    BODY_REFS[key] = b
    F = C(fop)
    lname = 'kernel_accepts_tc_in_nat_bitwiseaux_%s_fold' % fop.split('.')[1].lower()
    e0 = app(C(key), F, lit('f'), lit('m'), lit('n'))
    c1 = delta(e0, key, b, bhyp(key))
    fr = trans(c1, betas(c1.rhs, 2))
    head, args = spine(fr.rhs)
    M, z, s = args[0], args[1], args[2]
    N.name_param('accepts_tc_nat_bitwiseaux_%s_scase' % fop.split('.')[1].lower(), s, [])

    def lhs(v, x, y):
        return N.natrec_app(M, z, s, lit(v), lit(x), lit(y))

    meta = lambda v, x, y: '(Nat.bitwiseAux %s %s %s %s)' % (fop, v, x, y)

    def mot(v):
        return 'forall (m : Nat) (n : Nat), KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v, 'm', 'n')), pr(lit(meta(v, 'm', 'n'))))
    c1 = N.major_to_ctor_zero(lhs('Nat.zero', 'm', 'n'))
    c2 = N.iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 5)
    assert eq(c3.rhs, ZERO), pr(c3.rhs)
    base_ = 'fun (m : Nat) (n : Nat) => %s' % retype_rhs(chain([c1, c2, c3, symm(lit_zero())]), lit(meta('Nat.zero', 'm', 'n'))).proof
    d1 = N.major_to_ctor_succ(lhs('(Nat.succ g)', 'm', 'n'), 'g')
    d2 = N.iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 8)
    t = d3.rhs
    convs = []
    # the four div2 occurrences, the two recursive calls, the two sums
    div2 = lambda x: bcall('Nat.div2', [x], app(C('Nat.div2'), lit(x)), lit('(Nat.div2 %s)' % x))
    for path, x in (([0, 0, 4], 'm'), ([0, 0, 5], 'n'), ([0, 1, 4], 'm'), ([0, 1, 5], 'n')):
        c = at_path(t, path, div2(x))
        convs.append(c)
        t = c.rhs
    V = meta('g', '(Nat.div2 m)', '(Nat.div2 n)')
    ihc = Conv(lhs('g', '(Nat.div2 m)', '(Nat.div2 n)'), lit(V), '(ih (Nat.div2 m) (Nat.div2 n))')
    for path in ([0, 0], [0, 1]):
        c = at_path(t, path, ihc)
        convs.append(c)
        t = c.rhs
    c = at_path(t, [0], N.call('Nat.add', V, V))
    convs.append(c)
    t = c.rhs
    # the bits: testBit x Nat.zero (the zero literal first)
    for path, x in (([1, 0, 0], 'm'), ([1, 0, 1], 'n')):
        c = at_path(t, path + [1], symm(lit_zero()))
        convs.append(c)
        t = c.rhs
        c = at_path(t, path, testbit_call(x))
        convs.append(c)
        t = c.rhs
    bx, by = '(Nat.testBit m Nat.zero)', '(Nat.testBit n Nat.zero)'
    c = at_path(t, [1, 0], bcall(fop, [bx, by], app(F, blit(bx), blit(by)), blit('(%s %s %s)' % (fop, bx, by))))
    convs.append(c)
    t = c.rhs
    fv = '(%s %s %s)' % (fop, bx, by)
    c = at_path(t, [1], bcall('Nat.ofBool', [fv], app(C('Nat.ofBool'), blit(fv)), lit('(Nat.ofBool %s)' % fv)))
    convs.append(c)
    t = c.rhs
    convs.append(N.call('Nat.add', '(Nat.add %s %s)' % (V, V), '(Nat.ofBool %s)' % fv))
    step = 'fun (m : Nat) (n : Nat) => %s' % retype_rhs(chain([d1, d2, d3] + convs), lit(meta('(Nat.succ g)', 'm', 'n'))).proof
    rec = '(%s m n)' % N.nat_rec_proof('f', mot, base_, 'g', 'ih', step)
    whole = trans(fr, Conv(fr.rhs, lit(meta('f', 'm', 'n')), rec))
    ty = 'forall %s (f : Nat) (m : Nat) (n : Nat) %s, %s' % (N.HDR, bprem_decl(key), whole.ty())
    N.add_thm(lname, ty, 'fun %s (f : Nat) (m : Nat) (n : Nat) %s => %s' % (N.HDR, bprem_decl(key), whole.proof))
    return lname


BODY_REFS = {}


def gen_bitwise_family():
    out = {}
    for op, fop in (('Nat.land', 'Bool.and'), ('Nat.lor', 'Bool.or'), ('Nat.xor', 'Bool.xor')):
        aux = gen_bitwiseaux(fop)
        # bitwise F m n
        key = 'Nat.bitwise'
        CLOSURE[key] = [key, 'Nat.bitwiseAux', 'Nat.div2', 'Nat.testBit', 'Nat.ofBool', fop, 'Nat.add']
        b = BODY_REFS.get(key) or bbody(key)
        BODY_REFS[key] = b
        F = C(fop)
        e0 = app(C(key), F, lit('m'), lit('n'))
        c1 = delta(e0, key, b, bhyp(key))
        fr = trans(c1, betas(c1.rhs, 3))
        c2 = at_arg(fr.rhs, 1, N.call('Nat.add', 'm', 'n'))
        aux_call = Conv(app(C('Nat.bitwiseAux'), F, lit('(Nat.add m n)'), lit('m'), lit('n')),
                        lit('(Nat.bitwiseAux %s (Nat.add m n) m n)' % fop),
                        '(%s R tenv G (Nat.add m n) m n %s)' % (aux, bprem_args('Nat.bitwiseAux')))
        whole = retype_rhs(chain([fr, c2, aux_call]), lit('(Nat.bitwise %s m n)' % fop))
        lname = 'kernel_accepts_tc_in_nat_bitwise_%s_fold' % fop.split('.')[1].lower()
        ty = 'forall %s (m : Nat) (n : Nat) %s, %s' % (N.HDR, bprem_decl(key), whole.ty())
        N.add_thm(lname, ty, 'fun %s (m : Nat) (n : Nat) %s => %s' % (N.HDR, bprem_decl(key), whole.proof))
        # land / lor / xor
        CLOSURE[op] = [op, 'Nat.bitwise', 'Nat.bitwiseAux', 'Nat.div2', 'Nat.testBit', 'Nat.ofBool', fop, 'Nat.add']
        bo = bbody(op)
        fr2 = bfront(op, bo, [lit('a'), lit('b')])
        call = Conv(app(C(key), F, lit('a'), lit('b')), lit('(Nat.bitwise %s a b)' % fop),
                    '(%s R tenv G a b %s)' % (lname, bprem_args(key)))
        bregister(op, '(a : Nat) (b : Nat)', retype_rhs(chain([fr2, call]), lit('(%s a b)' % op)))


def bw_items():
    base()
    gen_bools()
    gen_ofbool()
    gen_toboolpar()
    gen_fst_snd()
    gen_div2pair()
    gen_div2('Nat.div2', 0)
    gen_div2('Nat.div2Par', 1)
    gen_iterdiv2()
    gen_shiftright()
    gen_testbit()
    gen_bitwise_family()
