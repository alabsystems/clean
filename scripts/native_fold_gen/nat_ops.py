"""Generate the native-Nat fold lemmas (KernelAcceptsTcIn derivations)."""
import json
import sys

from kx import (blit, C, app, lam, pi, bv, lit, ref, pr, spine, unref, inst, eq, Conv, refl, symm, trans, chain,
                appcong, app_l, app_r, at_arg, lit_zero, lit_succ, raw, beta, betas, delta, iota, retype_rhs, retype_lhs,
                Rec, LV1, NIL_LV, sx_str)
import canon

HDR = '(R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn)'
HDR_ARGS = 'R tenv G'

NAT = C('Nat')
ZERO = C('Nat.zero')
SUCC = C('Nat.succ')

# ---------------------------------------------------------------- canonical data
NATREC_TAG_NAME = 'Nat.rec'


def rule_def(rule_const, rec_name, ctor):
    from kx import NAME2TAG
    nf, rhs = canon.rule_rhs(NAME2TAG[rec_name], ctor)
    return nf, rhs, 'def %s : RecRule := RecRule.mk kcre_name_@@%s@@ kcre_nat_%d %s' % (rule_const, ctor, nf, pr(rhs))


NR_Z_NF, NR_Z_RHS, NR_Z_DEF = rule_def('accepts_tc_nat_rec_zero_rule', 'Nat.rec', 'Nat.zero')
NR_S_NF, NR_S_RHS, NR_S_DEF = rule_def('accepts_tc_nat_rec_succ_rule', 'Nat.rec', 'Nat.succ')

NATREC = Rec('Nat.rec', 'kcre_rec_meta_@@Nat.rec@@',
             {'Nat.zero': (NR_Z_NF, NR_Z_RHS), 'Nat.succ': (NR_S_NF, NR_S_RHS)},
             'kcre_name_@@u@@', 'hm', {'Nat.zero': 'hz', 'Nat.succ': 'hs'})
NATREC.prefix = 3
NATREC_RULES = {'Nat.zero': 'accepts_tc_nat_rec_zero_rule', 'Nat.succ': 'accepts_tc_nat_rec_succ_rule'}

P_NATREC = ('(hm : Eq (OptionType RecMeta) (recmeta_for (red_rec R) kcre_name_@@Nat.rec@@) '
            '(OptionType.some RecMeta kcre_rec_meta_@@Nat.rec@@)) '
            '(hz : Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Nat.rec@@ kcre_name_@@Nat.zero@@) '
            '(OptionType.some RecRule accepts_tc_nat_rec_zero_rule)) '
            '(hs : Eq (OptionType RecRule) (recrule_for (red_rec R) kcre_name_@@Nat.rec@@ kcre_name_@@Nat.succ@@) '
            '(OptionType.some RecRule accepts_tc_nat_rec_succ_rule))')
A_NATREC = 'hm hz hs'


def body_const(op):
    return 'accepts_tc_%s_body' % op.lower().replace('.', '_')


def hyp(op):
    return 'h' + op.split('.')[-1].lower()


def p_body(op):
    return '(%s : Eq (OptionType KExpr) (kdef_value_at (red_def R) kcre_name_@@%s@@ (ListType.nil Level)) (OptionType.some KExpr %s))' % (
        hyp(op), op, body_const(op))


def natrec_app(M, z, s, major, *extras):
    return app(C('Nat.rec', LV1), M, z, s, major, *extras)


def iota_nat(e):
    return iota(e, NATREC, '(Level.succ Level.zero)', NATREC_RULES)


def major_to_ctor_zero(e):
    """rewrite the Nat.rec major literal 0 to Nat.zero"""
    return at_arg(e, 3, lit_zero())


def major_to_ctor_succ(e, k):
    return at_arg(e, 3, lit_succ(k))


def name_pieces(prefix, M, z, s):
    from kx import name_term
    for suffix, t in (('motive', M), ('zcase', z), ('scase', s)):
        if t[0] in ('lam', 'pi', 'app'):
            add_def('def %s_%s : KExpr := %s' % (prefix, suffix, pr(t)), '%s_%s' % (prefix, suffix))
            name_term('%s_%s' % (prefix, suffix), t)


def nat_rec_proof(var, motive_ty, base, step_var, ih_name, step):
    return '(Nat.rec (fun (%s : Nat) => %s) (%s) (fun (%s : Nat) (%s : %s) => %s) %s)' % (
        var, motive_ty(var), base, step_var, ih_name, motive_ty(step_var), step, var)


# ---------------------------------------------------------------- items
ITEMS = []


def add_def(src, name):
    ITEMS.append({'kind': 'def', 'name': name, 'source': src})


def add_thm(name, ty, body):
    ITEMS.append({'kind': 'theorem', 'name': name, 'ty': ty, 'body': body})


IOTA_LOOKUP_TY = (
    'forall (env : RecEnv) (e : KExpr) (rn : Name) (mta : RecMeta) (major : KExpr) (cn : Name) (rule : RecRule) (r : KExpr), '
    'Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name rn) -> '
    'Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta mta) -> '
    'Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) -> '
    'Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cn) -> '
    'Eq (OptionType RecRule) (recrule_for env rn cn) (OptionType.some RecRule rule) -> '
    'Eq (OptionType KExpr) (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) (OptionType.some KExpr r) -> '
    'Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r)')
IOTA_LOOKUP_BODY = (
    'fun (env : RecEnv) (e : KExpr) (rn : Name) (mta : RecMeta) (major : KExpr) (cn : Name) (rule : RecRule) (r : KExpr) '
    '(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name rn)) '
    '(hmeta : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta mta)) '
    '(hmajor : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major)) '
    '(hcn : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cn)) '
    '(hrule : Eq (OptionType RecRule) (recrule_for env rn cn) (OptionType.some RecRule rule)) '
    '(hcontr : Eq (OptionType KExpr) (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) (OptionType.some KExpr r)) => '
    'opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn e)) '
    '(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) (fun (mta0 : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta0) (kapp_args e))) (fun (major0 : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major0)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule0 : RecRule) => iota_contractum_at mta0 rule0 (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major0)))))) '
    'rn r hhead '
    '(opt_bind_some_intro RecMeta KExpr (recmeta_for env rn) '
    '(fun (mta0 : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (iota_major_index mta0) (kapp_args e))) (fun (major0 : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major0)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env rn cname) (fun (rule0 : RecRule) => iota_contractum_at mta0 rule0 (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major0))))) '
    'mta r hmeta '
    '(opt_bind_some_intro KExpr KExpr (list_head (list_drop (iota_major_index mta) (kapp_args e))) '
    '(fun (major0 : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major0)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env rn cname) (fun (rule0 : RecRule) => iota_contractum_at mta rule0 (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major0)))) '
    'major r hmajor '
    '(opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn major)) '
    '(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env rn cname) (fun (rule0 : RecRule) => iota_contractum_at mta rule0 (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))) '
    'cn r hcn '
    '(opt_bind_some_intro RecRule KExpr (recrule_for env rn cn) '
    '(fun (rule0 : RecRule) => iota_contractum_at mta rule0 (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) '
    'rule r hrule hcontr))))')


KA = 'KernelAcceptsTcIn R tenv Bool.false G'
HELPERS = [
    ('accepts_tc_beta',
     'forall %s (A : KExpr) (b : KExpr) (a : KExpr), %s (KExpr.app (KExpr.lam A b) a) (instantiate b a)' % (HDR, KA),
     'fun %s (A : KExpr) (b : KExpr) (a : KExpr) => KernelAcceptsTcIn.cdp R tenv G (KExpr.app (KExpr.lam A b) a) (instantiate b a) '
     '(DefEqCDPIn.raw R (KExpr.app (KExpr.lam A b) a) (instantiate b a) (par_reduces_cdp.beta R A A b b a a '
     '(par_reduces_cdp.refl R A) (par_reduces_cdp.refl R b) (par_reduces_cdp.refl R a)))' % HDR),
    ('accepts_tc_app_l',
     'forall %s (f : KExpr) (f2 : KExpr) (a : KExpr), %s f f2 -> %s (KExpr.app f a) (KExpr.app f2 a)' % (HDR, KA, KA),
     'fun %s (f : KExpr) (f2 : KExpr) (a : KExpr) (h : %s f f2) => KernelAcceptsTcIn.app_cong R tenv G f f2 a a h '
     '(KernelAcceptsTcIn.cdp R tenv G a a (DefEqCDPIn.refl R a))' % (HDR, KA)),
    ('accepts_tc_app_r',
     'forall %s (f : KExpr) (a : KExpr) (a2 : KExpr), %s a a2 -> %s (KExpr.app f a) (KExpr.app f a2)' % (HDR, KA, KA),
     'fun %s (f : KExpr) (a : KExpr) (a2 : KExpr) (h : %s a a2) => KernelAcceptsTcIn.app_cong R tenv G f f a a2 '
     '(KernelAcceptsTcIn.cdp R tenv G f f (DefEqCDPIn.refl R f)) h' % (HDR, KA)),
    ('accepts_tc_delta',
     'forall %s (e : KExpr) (n : Name) (v : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n) -> '
     'Eq (OptionType KExpr) (kdef_value_at (red_def R) n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr v) -> '
     '%s e (apply_spine (kapp_args e) v)' % (HDR, KA),
     'fun %s (e : KExpr) (n : Name) (v : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)) '
     '(hv : Eq (OptionType KExpr) (kdef_value_at (red_def R) n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr v)) => '
     'KernelAcceptsTcIn.cdp R tenv G e (apply_spine (kapp_args e) v) (DefEqCDPIn.raw R e (apply_spine (kapp_args e) v) '
     '(par_reduces_cdp.delta R e (apply_spine (kapp_args e) v) (delta_reduct_of_value_some (red_def R) e n v hh hv)))' % HDR),
]
IOTA_TY = ('forall %s (e : KExpr) (rn : Name) (mta : RecMeta) (major : KExpr) (cn : Name) (rule : RecRule) (r : KExpr), '
           'Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name rn) -> '
           'Eq (OptionType RecMeta) (recmeta_for (red_rec R) rn) (OptionType.some RecMeta mta) -> '
           'Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major) -> '
           'Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cn) -> '
           'Eq (OptionType RecRule) (recrule_for (red_rec R) rn cn) (OptionType.some RecRule rule) -> '
           'Eq (OptionType KExpr) (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) (OptionType.some KExpr r) -> '
           '%s e r') % (HDR, KA)
IOTA_BODY = ('fun %s (e : KExpr) (rn : Name) (mta : RecMeta) (major : KExpr) (cn : Name) (rule : RecRule) (r : KExpr) '
             '(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name rn)) '
             '(h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec R) rn) (OptionType.some RecMeta mta)) '
             '(h3 : Eq (OptionType KExpr) (list_head (list_drop (iota_major_index mta) (kapp_args e))) (OptionType.some KExpr major)) '
             '(h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cn)) '
             '(h5 : Eq (OptionType RecRule) (recrule_for (red_rec R) rn cn) (OptionType.some RecRule rule)) '
             '(h6 : Eq (OptionType KExpr) (iota_contractum_at mta rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)) (OptionType.some KExpr r)) => '
             'KernelAcceptsTcIn.cdp R tenv G e r (DefEqCDPIn.raw R e r (par_reduces_cdp.iota R e r '
             '(accepts_tc_iota_reduct_of_lookup (red_rec R) e rn mta major cn rule r h1 h2 h3 h4 h5 h6)))') % HDR


def base_items():
    add_thm('accepts_tc_iota_reduct_of_lookup', IOTA_LOOKUP_TY, IOTA_LOOKUP_BODY)
    for n, t, b in HELPERS:
        add_thm(n, t, b)
    add_thm('accepts_tc_iota', IOTA_TY, IOTA_BODY)
    add_def(NR_Z_DEF, 'accepts_tc_nat_rec_zero_rule')
    add_def(NR_S_DEF, 'accepts_tc_nat_rec_succ_rule')
    # the canonical Nat.rec data IS the reflected seed's: each is a computation over kernel_core_red_env
    add_thm('accepts_tc_nat_rec_meta_reflected',
            'Eq (OptionType RecMeta) (recmeta_for (red_rec kernel_core_red_env) kcre_name_@@Nat.rec@@) (OptionType.some RecMeta kcre_rec_meta_@@Nat.rec@@)',
            'Eq.refl (OptionType RecMeta) (OptionType.some RecMeta kcre_rec_meta_@@Nat.rec@@)')
    for ctor, rule in (('Nat.zero', 'accepts_tc_nat_rec_zero_rule'), ('Nat.succ', 'accepts_tc_nat_rec_succ_rule')):
        add_thm(rule + '_reflected',
                'Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) kcre_name_@@Nat.rec@@ kcre_name_@@%s@@) (OptionType.some RecRule %s)' % (ctor, rule),
                'Eq.refl (OptionType RecRule) (OptionType.some RecRule %s)' % rule)
    from kx import inst_levels, name_term
    for nm, rhs in (('accepts_tc_nat_rec_zero_rhs1', NR_Z_RHS), ('accepts_tc_nat_rec_succ_rhs1', NR_S_RHS)):
        t = inst_levels(rhs, 'kcre_name_@@u@@', '(Level.succ Level.zero)')
        add_def('def %s : KExpr := %s' % (nm, pr(t)), nm)
        name_term(nm, t)


MODE = {'emit': False}


def emit_body(op, b):
    if MODE['emit']:
        ITEMS.append({'kind': 'reflect_body', 'name': body_const(op), 'of': op})
    else:
        add_def('def %s : KExpr := %s' % (body_const(op), pr(b)), body_const(op))


def body_item(op):
    b = canon.body(op)
    emit_body(op, b)
    return b


def binop_front(op, b_ast, a_payload, b_payload):
    """Nat.op (lit a) (lit b) --delta, beta, beta--> reduced body"""
    e0 = app(C(op), lit(a_payload), lit(b_payload))
    body_ref = ref(body_const(op), b_ast)
    c1 = delta(e0, op, body_ref, hyp(op))
    c2 = betas(c1.rhs, 2)
    return trans(c1, c2)


def unop_front(op, b_ast, x_payload):
    e0 = app(C(op), lit(x_payload))
    body_ref = ref(body_const(op), b_ast)
    c1 = delta(e0, op, body_ref, hyp(op))
    c2 = betas(c1.rhs, 1)
    return trans(c1, c2)


# ---------------------------------------------------------------- op registry
ORDER = ['Nat.pred', 'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.shiftLeft', 'Nat.divCore', 'Nat.div',
         'Nat.modCore', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.div2', 'Nat.testBit', 'Nat.ofBool', 'Nat.bitwiseAux',
         'Nat.bitwise', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftRight']
CLOSURE = {}


def short(op):
    return op.split('.')[1].lower()


def lemma_name(op):
    return 'kernel_accepts_tc_in_nat_%s_fold' % short(op)


def closure_sorted(op):
    return sorted(CLOSURE[op], key=ORDER.index)


def prem_decl(op):
    return P_NATREC + ' ' + ' '.join(p_body(o) for o in closure_sorted(op))


def prem_args(op):
    return A_NATREC + ' ' + ' '.join(hyp(o) for o in closure_sorted(op))


def call(op, *xs):
    return Conv(app(C(op), *[lit(x) for x in xs]), lit('(%s %s)' % (op, ' '.join(xs))),
                '(%s R tenv G %s %s)' % (lemma_name(op), ' '.join(xs), prem_args(op)))


def register(op, params, whole):
    binders = ' '.join('(%s : Nat)' % p for p in params)
    ty = 'forall %s %s %s, %s' % (HDR, binders, prem_decl(op), whole.ty())
    add_thm(lemma_name(op), ty, 'fun %s %s %s => %s' % (HDR, binders, prem_decl(op), whole.proof))


def name_param(prefix, t, params):
    """name a term that may mention literal parameters (printed as (name p1 p2))"""
    from kx import name_term
    if t[0] not in ('lam', 'pi', 'app'):
        return
    binders = ' '.join('(%s : Nat)' % p for p in params)
    add_def('def %s %s : KExpr := %s' % (prefix, binders, pr(t)), prefix)
    call_s = '(%s %s)' % (prefix, ' '.join(params)) if params else prefix
    name_term(call_s, t)


def two_conv():
    """Nat.succ (Nat.succ Nat.zero) == literal 2"""
    c1 = app_r(SUCC, app_r(SUCC, symm(lit_zero())))
    c2 = app_r(SUCC, symm(lit_succ('Nat.zero')))
    c3 = symm(lit_succ('(Nat.succ Nat.zero)'))
    return chain([c1, c2, c3])


# ---------------------------------------------------------------- succ: a constructor, its fold IS lit_succ
def gen_succ():
    c = symm(lit_succ('x'))
    ty = 'forall %s (x : Nat), %s' % (HDR, c.ty())
    add_thm('kernel_accepts_tc_in_nat_succ_fold', ty, 'fun %s (x : Nat) => %s' % (HDR, c.proof))


# ---------------------------------------------------------------- pred
def gen_pred():
    CLOSURE['Nat.pred'] = ['Nat.pred']
    b = body_item('Nat.pred')
    front = unop_front('Nat.pred', b, 'x')
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    name_param('accepts_tc_nat_pred_motive', M, [])
    name_param('accepts_tc_nat_pred_scase', s, [])
    front = unop_front('Nat.pred', b, 'x')

    def nr_at(v):
        return natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(nr_at(v)), pr(lit('(Nat.pred %s)' % v)))

    e = nr_at('Nat.zero')
    c1 = major_to_ctor_zero(e)
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    base = retype_rhs(chain([c1, c2, c3, symm(lit_zero())]), lit('(Nat.pred Nat.zero)'))
    e = nr_at('(Nat.succ k)')
    d1 = major_to_ctor_succ(e, 'k')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    assert eq(d3.rhs, lit('k')), pr(d3.rhs)
    step = retype_rhs(chain([d1, d2, d3]), lit('(Nat.pred (Nat.succ k))'))
    rec = nat_rec_proof('x', mot, base.proof, 'k', '_ih', step.proof)
    register('Nat.pred', ['x'], trans(front, Conv(front.rhs, lit('(Nat.pred x)'), rec)))


# ---------------------------------------------------------------- add / sub (the spec's own: Nat.rec on the
# second argument into Nat -> Nat, applied to the first)
def gen_spec_rec(op, wrap_op):
    """wrap_op: None (add: succ) or ('Nat.pred') (sub)"""
    b = body_item(op)
    front = binop_front(op, b, 'a', 'b')
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    pre = 'accepts_tc_nat_%s' % short(op)
    name_param(pre + '_motive', M, [])
    name_param(pre + '_zcase', z, [])
    name_param(pre + '_scase', s, [])
    front = binop_front(op, b, 'a', 'b')

    def lhs(v):
        return natrec_app(M, z, s, lit(v), lit('a'))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(lit('(%s a %s)' % (op, v))))

    e = lhs('Nat.zero')
    c1 = major_to_ctor_zero(e)
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 4)
    assert eq(c3.rhs, lit('a')), pr(c3.rhs)
    base = retype_rhs(chain([c1, c2, c3]), lit('(%s a Nat.zero)' % op))
    e = lhs('(Nat.succ k)')
    d1 = major_to_ctor_succ(e, 'k')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 7)
    ih = Conv(lhs('k'), lit('(%s a k)' % op), 'ih')
    if wrap_op is None:
        assert eq(d3.rhs, app(SUCC, lhs('k'))), pr(d3.rhs)
        d4 = app_r(SUCC, ih)
        d5 = symm(lit_succ('(%s a k)' % op))
        tail = [d4, d5]
    else:
        assert eq(d3.rhs, app(C(wrap_op), lhs('k'))), pr(d3.rhs)
        d4 = app_r(C(wrap_op), ih)
        d5 = call(wrap_op, '(%s a k)' % op)
        tail = [d4, d5]
    step = retype_rhs(chain([d1, d2, d3] + tail), lit('(%s a (Nat.succ k))' % op))
    rec = nat_rec_proof('b', mot, base.proof, 'k', 'ih', step.proof)
    register(op, ['a', 'b'], trans(front, Conv(front.rhs, lit('(%s a b)' % op), rec)))


def gen_add():
    CLOSURE['Nat.add'] = ['Nat.add']
    gen_spec_rec('Nat.add', None)


def gen_sub():
    CLOSURE['Nat.sub'] = ['Nat.sub', 'Nat.pred']
    gen_spec_rec('Nat.sub', 'Nat.pred')


# ---------------------------------------------------------------- kernel-built ops (init_nat): Nat.rec on the
# second argument, Nat-valued, first argument inside the cases
BODIES = {}
NATNAT = lam(NAT, NAT)
TWO = app(SUCC, app(SUCC, ZERO))


def kbody(z, s):
    return lam(NAT, lam(NAT, natrec_app(NATNAT, z, s, bv(0))))


BODIES['Nat.mul'] = kbody(ZERO, lam(NAT, lam(NAT, app(C('Nat.add'), bv(0), bv(3)))))
BODIES['Nat.pow'] = kbody(app(SUCC, ZERO), lam(NAT, lam(NAT, app(C('Nat.mul'), bv(0), bv(3)))))
BODIES['Nat.shiftLeft'] = kbody(bv(1), lam(NAT, lam(NAT, app(C('Nat.mul'), bv(0), TWO))))


def hand_body_item(op):
    b = BODIES[op]
    emit_body(op, b)
    return b


def one_conv():
    """Nat.succ Nat.zero == literal 1"""
    return chain([app_r(SUCC, symm(lit_zero())), symm(lit_succ('Nat.zero'))])


def gen_kernel_rec(op, inner, base_tail, step_tail):
    """inner: the op the successor case applies (add/mul); base_tail(conv at z) -> list of convs"""
    b = hand_body_item(op)
    front = binop_front(op, b, 'a', 'b')
    head, args = spine(front.rhs)
    M, z, s = args[0], args[1], args[2]
    pre = 'accepts_tc_nat_%s' % short(op)
    name_param(pre + '_scase', s, ['a'])
    front = binop_front(op, b, 'a', 'b')

    def lhs(v):
        return natrec_app(M, z, s, lit(v))

    def mot(v):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(lhs(v)), pr(lit('(%s a %s)' % (op, v))))

    e = lhs('Nat.zero')
    c1 = major_to_ctor_zero(e)
    c2 = iota_nat(c1.rhs)
    c3 = betas(c2.rhs, 3)
    base = retype_rhs(chain([c1, c2, c3] + base_tail(c3.rhs)), lit('(%s a Nat.zero)' % op))
    e = lhs('(Nat.succ k)')
    d1 = major_to_ctor_succ(e, 'k')
    d2 = iota_nat(d1.rhs)
    d3 = betas(d2.rhs, 6)
    ih = Conv(lhs('k'), lit('(%s a k)' % op), 'ih')
    step = retype_rhs(chain([d1, d2, d3] + step_tail(d3.rhs, ih)), lit('(%s a (Nat.succ k))' % op))
    rec = nat_rec_proof('b', mot, base.proof, 'k', 'ih', step.proof)
    register(op, ['a', 'b'], trans(front, Conv(front.rhs, lit('(%s a b)' % op), rec)))


def gen_mul():
    CLOSURE['Nat.mul'] = ['Nat.mul', 'Nat.add']

    def base_tail(t):
        assert eq(t, ZERO), pr(t)
        return [symm(lit_zero())]

    def step_tail(t, ih):
        assert eq(t, app(C('Nat.add'), ih.lhs, lit('a'))), pr(t)
        return [app_l(app_r(C('Nat.add'), ih), lit('a')), call('Nat.add', '(Nat.mul a k)', 'a')]
    gen_kernel_rec('Nat.mul', 'Nat.add', base_tail, step_tail)


def gen_pow():
    CLOSURE['Nat.pow'] = ['Nat.pow', 'Nat.mul', 'Nat.add']

    def base_tail(t):
        assert eq(t, app(SUCC, ZERO)), pr(t)
        return [one_conv()]

    def step_tail(t, ih):
        assert eq(t, app(C('Nat.mul'), ih.lhs, lit('a'))), pr(t)
        return [app_l(app_r(C('Nat.mul'), ih), lit('a')), call('Nat.mul', '(Nat.pow a k)', 'a')]
    gen_kernel_rec('Nat.pow', 'Nat.mul', base_tail, step_tail)


def gen_shl():
    CLOSURE['Nat.shiftLeft'] = ['Nat.shiftLeft', 'Nat.mul', 'Nat.add']

    def base_tail(t):
        assert eq(t, lit('a')), pr(t)
        return []

    def step_tail(t, ih):
        assert eq(t, app(C('Nat.mul'), ih.lhs, TWO)), pr(t)
        c1 = app_l(app_r(C('Nat.mul'), ih), TWO)
        c2 = app_r(app(C('Nat.mul'), lit('(Nat.shiftLeft a k)')), two_conv())
        c3 = call('Nat.mul', '(Nat.shiftLeft a k)', '(Nat.succ (Nat.succ Nat.zero))')
        return [c1, c2, c3]
    gen_kernel_rec('Nat.shiftLeft', 'Nat.mul', base_tail, step_tail)
