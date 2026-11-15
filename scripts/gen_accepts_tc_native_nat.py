#!/usr/bin/env python3
"""Mint the E4d native-fold artifact: crates/clean-verify/src/spec/core_spec/generated/accepts_tc_native_nat.json.

The deployed kernel folds a canonical Nat / Int head applied to literals in one step (reduce_nat,
reduce_int, reduce_int_pred_fold). This generator prints, for each fold key the specification world
admits, a KernelAcceptsTcIn derivation of the fold by delta / beta / iota / projection-beta and the
literal rules alone, over any reduction environment that holds the canonical closure, plus witness
environments and instances. It is OUTSIDE the trusted base: the Clean kernel re-checks every term at
registration (acceptance_cdp_in/native_nat.rs), and every canonical body / recursor is reflected from
the live environment there, never taken from this script.

    python3 scripts/gen_accepts_tc_native_nat.py            # rewrite the artifact
    python3 scripts/gen_accepts_tc_native_nat.py --check    # exit 1 if the artifact is stale
    python3 scripts/gen_accepts_tc_native_nat.py --hand-bodies OUT.json
        # the same terms with the canonical bodies / Int.rec printed inline (for a scratch driver
        # that cannot reflect), Nat part omitted

The modules under scripts/native_fold_gen/ carry the term algebra (kx), the reflected-core reader
(canon), and one generator per family (nat_ops / nat_cmp_div, int_ops / int_arith, bw_ops /
bw_family). Names print as kcre_name_@@<real name>@@ placeholders, resolved at registration.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / 'native_fold_gen'))

import kx  # noqa: E402
import nat_ops as N  # noqa: E402
import nat_cmp_div as NC  # noqa: E402
import int_ops as I  # noqa: E402
import int_arith as IA  # noqa: E402
import bw_ops as B  # noqa: E402
import bw_family as BF  # noqa: E402
from kx import C, app, lit, pi, lam, bv  # noqa: E402

ARTIFACT = (Path(__file__).resolve().parents[1]
            / 'crates/clean-verify/src/spec/core_spec/generated/accepts_tc_native_nat.json')
NAT, INT, BOOL = N.NAT, I.INT, B.BOOL


def pr(t):
    return kx.pr(t)


def nat_term(n):
    return NC.nat_term(n)


def int_payload(v):
    return '(Int.ofNat %s)' % nat_term(v) if v >= 0 else '(Int.negSucc %s)' % nat_term(-v - 1)


def int_env_and_instances():
    defenv = '(red_def accepts_tc_nat_fold_env)'
    types = {'Int.neg': pi(INT, INT), 'Int.negOfNat': pi(NAT, INT), 'Int.subNatNat': pi(NAT, pi(NAT, INT)),
             'Int.add': pi(INT, pi(INT, INT)), 'Int.sub': pi(INT, pi(INT, INT)), 'Int.mul': pi(INT, pi(INT, INT))}
    for op in I.INT_ORDER:
        if op not in types:  # Int.toNat is Nat-valued and needs no witness in this int-arith env
            continue
        defenv = '(DefEnv.addDef %s kcre_name_@@%s@@ (KDefSig.mk (KConstSig.mk (ListType.nil Name) %s) %s))' % (
            defenv, op, pr(types[op]), I.ibody_const(op))
    recenv = ('(RecEnv.addRec (red_rec kernel_core_red_env) kcre_name_@@Int.rec@@ accepts_tc_int_rec_meta '
              '(RecRules.cons accepts_tc_int_rec_ofnat_rule (RecRules.cons accepts_tc_int_rec_negsucc_rule RecRules.nil)))')
    N.add_def('def accepts_tc_int_fold_env : RedEnv := RedEnv.mk %s %s (red_ind_ctor kernel_core_red_env)' % (recenv, defenv),
              'accepts_tc_int_fold_env')
    env = 'accepts_tc_int_fold_env'
    refl = lambda ty, v: '(Eq.refl (OptionType %s) (OptionType.some %s %s))' % (ty, ty, v)
    base = [refl('RecMeta', 'kcre_rec_meta_@@Nat.rec@@'), refl('RecRule', 'accepts_tc_nat_rec_zero_rule'),
            refl('RecRule', 'accepts_tc_nat_rec_succ_rule'), refl('RecMeta', 'accepts_tc_int_rec_meta'),
            refl('RecRule', 'accepts_tc_int_rec_ofnat_rule'), refl('RecRule', 'accepts_tc_int_rec_negsucc_rule')]
    for op, args in (('Int.add', (2, -5)), ('Int.sub', (-3, 4)), ('Int.mul', (-2, -3)), ('Int.neg', (4,))):
        nat = sorted(I.NAT_NEEDS.get(op, []), key=N.ORDER.index)
        ints = sorted(I.INT_CLOSURE[op], key=I.INT_ORDER.index)
        prems = ' '.join(base + [refl('KExpr', N.body_const(o)) for o in nat] + [refl('KExpr', I.ibody_const(o)) for o in ints])
        ps = [int_payload(a) for a in args]
        lhs = app(C(op), *[I.ilit(p) for p in ps])
        rhs = I.ilit('(%s %s)' % (op, ' '.join(ps)))
        short = op.split('.')[1].lower()
        ty = 'forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn %s tenv Bool.false G %s %s' % (env, pr(lhs), pr(rhs))
        N.add_thm('accepts_tc_int_%s_instance' % short, ty,
                  'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => %s %s tenv G %s %s' % (I.ilemma(op), env, ' '.join(ps), prems))
        sty = ty.replace('KernelAcceptsTcIn %s' % env, 'TypingTcIn %s' % env)
        N.add_thm('accepts_tc_int_%s_instance_sound' % short, sty,
                  'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => kernel_accepts_tc_in_sound %s tenv Bool.false G %s %s (accepts_tc_int_%s_instance tenv G)' % (
                      env, pr(lhs), pr(rhs), short))
    # the predecessor fold, at a large count's shape (a small count here: the lemma is uniform in it)
    z, c = int_payload(3), nat_term(5)
    lhs = N.natrec_app(lam(NAT, INT), I.ilit(z), I.PRED_STEP, lit(c))
    rhs = I.ilit('(Nat.rec (fun (_ : Nat) => Int) %s (fun (_ : Nat) (ih : Int) => %s) %s)' % (z, I.pred_step_meta('ih'), c))
    ty = 'forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn %s tenv Bool.false G %s %s' % (env, pr(lhs), pr(rhs))
    N.add_thm('accepts_tc_int_pred_fold_instance', ty,
              'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => kernel_accepts_tc_in_int_pred_fold %s tenv G %s %s %s' % (env, z, c, ' '.join(base)))


BW_IN_CORE = ['Nat.add', 'Nat.sub', 'Nat.pred', 'Bool.and']


def bw_types():
    lvp = ('(ListType.cons Level (Level.param kcre_name_@@u@@) (ListType.cons Level (Level.param kcre_name_@@u_1@@) '
           '(ListType.nil Level)))')
    su = ('sort', '(Level.succ (Level.param kcre_name_@@u@@))')
    su1 = ('sort', '(Level.succ (Level.param kcre_name_@@u_1@@))')
    prod = C('Prod', lvp)
    bb2 = pi(BOOL, pi(BOOL, BOOL))
    nn = pi(NAT, pi(NAT, NAT))
    return {
        'Prod.fst': pi(su, pi(su1, pi(app(prod, bv(1), bv(0)), bv(2)))),
        'Prod.snd': pi(su, pi(su1, pi(app(prod, bv(1), bv(0)), bv(1)))),
        'Prod.mk': pi(su, pi(su1, pi(bv(1), pi(bv(1), app(prod, bv(3), bv(2)))))),
        'Nat.div2Pair': pi(NAT, app(C('Prod', B.LV00), NAT, NAT)),
        'Nat.div2': pi(NAT, NAT), 'Nat.div2Par': pi(NAT, NAT), 'Nat.iterDiv2': nn, 'Nat.shiftRight': nn,
        'Nat.toBoolPar': pi(NAT, BOOL), 'Nat.testBit': pi(NAT, pi(NAT, BOOL)), 'Nat.ofBool': pi(BOOL, NAT),
        'Bool.not': pi(BOOL, BOOL), 'Bool.or': bb2, 'Bool.xor': bb2,
        'Nat.bitwiseAux': pi(bb2, pi(NAT, pi(NAT, pi(NAT, NAT)))), 'Nat.bitwise': pi(bb2, nn),
        'Nat.land': nn, 'Nat.lor': nn, 'Nat.xor': nn,
    }


def bw_env_and_instances(start):
    types = bw_types()
    two = '(ListType.cons Name kcre_name_@@u@@ (ListType.cons Name kcre_name_@@u_1@@ (ListType.nil Name)))'
    defenv = '(red_def accepts_tc_nat_fold_env)'
    for op in B.ORDER:
        if op in BW_IN_CORE:
            continue
        params = two if op in B.LEVELS else '(ListType.nil Name)'
        defenv = '(DefEnv.addDef %s kcre_name_@@%s@@ (KDefSig.mk (KConstSig.mk %s %s) %s))' % (
            defenv, op, params, pr(types[op]), B.bbody_const(op))
    # the reflected core already holds Bool.and: its entry IS the canonical body
    N.add_thm('accepts_tc_bool_and_body_reflected',
              'Eq (OptionType KExpr) (kdef_value_at (red_def kernel_core_red_env) kcre_name_@@Bool.and@@ (ListType.nil Level)) (OptionType.some KExpr %s)' % B.bbody_const('Bool.and'),
              'Eq.refl (OptionType KExpr) (OptionType.some KExpr %s)' % B.bbody_const('Bool.and'))
    cm = '(KCtorMeta.mk (KConstSig.mk %s %s) kcre_name_@@Prod@@ (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)) Nat.zero)' % (
        two, pr(types['Prod.mk']))
    ind = '(IndCtorEnv.addCtor (red_ind_ctor kernel_core_red_env) kcre_name_@@Prod.mk@@ %s)' % cm
    N.add_def('def accepts_tc_bw_fold_env : RedEnv := RedEnv.mk (red_rec kernel_core_red_env) %s %s' % (defenv, ind),
              'accepts_tc_bw_fold_env')
    env = 'accepts_tc_bw_fold_env'
    refl = lambda ty, v: '(Eq.refl (OptionType %s) (OptionType.some %s %s))' % (ty, ty, v)
    for op, args in (('Nat.land', (6, 3)), ('Nat.lor', (5, 2)), ('Nat.xor', (6, 3)), ('Nat.shiftRight', (8, 1))):
        parts = [refl('RecMeta', 'kcre_rec_meta_@@Nat.rec@@'), refl('RecRule', 'accepts_tc_nat_rec_zero_rule'),
                 refl('RecRule', 'accepts_tc_nat_rec_succ_rule')]
        clo, nd = B.REGISTERED[op]
        if 'bool' in nd:
            parts += [refl('RecMeta', 'kcre_rec_meta_@@Bool.rec@@'), refl('RecRule', 'accepts_tc_bool_rec_false_rule'),
                      refl('RecRule', 'accepts_tc_bool_rec_true_rule')]
        if 'prod' in nd:
            parts += [cm, refl('KCtorMeta', cm), '(Eq.refl Nat (Nat.succ (Nat.succ Nat.zero)))']
        parts += [refl('KExpr', N.body_const(o) if o in ('Nat.add', 'Nat.sub', 'Nat.pred') else B.bbody_const(o)) for o in clo]
        ns = [nat_term(a) for a in args]
        lhs = app(C(op), *[lit(n) for n in ns])
        rhs = lit('(%s %s)' % (op, ' '.join(ns)))
        short = op.split('.')[1].lower()
        ty = 'forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn %s tenv Bool.false G %s %s' % (env, pr(lhs), pr(rhs))
        N.add_thm('accepts_tc_nat_%s_instance' % short, ty,
                  'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => %s %s tenv G %s %s' % (B.blemma(op), env, ' '.join(ns), ' '.join(parts)))
        sty = ty.replace('KernelAcceptsTcIn %s' % env, 'TypingTcIn %s' % env)
        N.add_thm('accepts_tc_nat_%s_instance_sound' % short, sty,
                  'fun (tenv : KDeclEnv) (G : ListType CtxEntryIn) => kernel_accepts_tc_in_sound %s tenv Bool.false G %s %s (accepts_tc_nat_%s_instance tenv G)' % (
                      env, pr(lhs), pr(rhs), short))


def generate(emit):
    """Every item in registration order, and the index where the Nat part ends."""
    N.MODE['emit'] = emit
    N.MODE['kflag'] = True
    NC.main_items()
    nat_end = len(N.ITEMS)
    IA.int_items()
    int_env_and_instances()
    start = len(N.ITEMS)
    BF.bw_items()
    bw_env_and_instances(start)
    if emit:
        for item in N.ITEMS[start:]:
            item['late'] = True
    return N.ITEMS, nat_end


def main(argv):
    if len(argv) >= 2 and argv[0] == '--hand-bodies':
        items, nat_end = generate(emit=False)
        Path(argv[1]).write_text(json.dumps(items[nat_end:], indent=1))
        return 0
    items, _ = generate(emit=True)
    text = json.dumps(items, indent=1)
    if argv == ['--check']:
        if ARTIFACT.read_text() != text:
            print('STALE: %s differs from the generator output; re-run without --check' % ARTIFACT)
            return 1
        print('OK: %s matches the generator (%d items)' % (ARTIFACT.name, len(items)))
        return 0
    if argv:
        print(__doc__)
        return 2
    ARTIFACT.write_text(text)
    print('wrote %s (%d items)' % (ARTIFACT, len(items)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
