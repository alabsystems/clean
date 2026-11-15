"""KExpr mirror + proof-term generator for the E4d native-fold lemmas.

Outside the TCB: every term it prints is re-checked by the Clean kernel.
Names are printed as kcre_name_@@<real name>@@ placeholders; the Rust side
(and the scratch driver) substitute the interning tag.
"""
import re
from pathlib import Path

GEN = str(Path(__file__).resolve().parents[2] / 'crates/clean-verify/src/spec/core_spec/generated') + '/'


def load_interning():
    tag2name = {}
    for line in open(GEN + 'kernel_core_red_env.interning.tsv'):
        t, n = line.rstrip('\n').split('\t')
        tag2name[int(t)] = n
    return tag2name


TAG2NAME = load_interning()
NAME2TAG = {v: k for k, v in TAG2NAME.items()}


SCRATCH_NAMES = {}


def subst_tags(s, extra=None):
    """Replace kcre_name_@@Name@@ by the interned atom; a name the table does not carry (scratch only)
    becomes a distinct two-component Name."""
    table = dict(NAME2TAG)
    if extra:
        table.update(extra)

    def name(m):
        n = m.group(1)
        if n in table:
            return 'kcre_name_%d' % table[n]
        if n not in SCRATCH_NAMES:
            SCRATCH_NAMES[n] = len(SCRATCH_NAMES) + 1
        return '(Name.str (Name.str Name.anonymous kcre_nat_7) kcre_nat_%d)' % SCRATCH_NAMES[n]
    s = re.sub(r'kcre_name_@@([^@]+)@@', name, s)
    return re.sub(r'@@([^@]+)@@', lambda m: str(table[m.group(1)]), s)


# ---------------------------------------------------------------- s-exprs
def tokenize(s):
    return re.findall(r'\(|\)|[^\s()]+', s)


def parse_sx(s):
    toks = tokenize(s)
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == '(':
            out = []
            while toks[pos] != ')':
                out.append(go())
            pos += 1
            return out
        return t
    r = go()
    assert pos == len(toks), (pos, len(toks))
    return r


def sx_str(sx):
    if isinstance(sx, str):
        return sx
    return '(' + ' '.join(sx_str(x) for x in sx) + ')'


def rename(atom):
    m = re.fullmatch(r'kcre_name_(\d+)', atom)
    if m:
        return 'kcre_name_@@%s@@' % TAG2NAME[int(m.group(1))]
    return atom


def sx_map_atoms(sx, f):
    if isinstance(sx, str):
        return f(sx)
    return [sx_map_atoms(x, f) for x in sx]


def natlit(atom):
    m = re.fullmatch(r'kcre_nat_(\d+)', atom)
    assert m, atom
    return int(m.group(1))


def conv(sx):
    """generated-syntax s-expr -> AST"""
    if isinstance(sx, str):
        raise ValueError('bare atom as KExpr: %s' % sx)
    h = sx[0]
    if h == 'KExpr.app':
        return ('app', conv(sx[1]), conv(sx[2]))
    if h == 'KExpr.lam':
        return ('lam', conv(sx[1]), conv(sx[2]))
    if h == 'KExpr.pi':
        return ('pi', conv(sx[1]), conv(sx[2]))
    if h == 'KExpr.let_':
        return ('let', conv(sx[1]), conv(sx[2]), conv(sx[3]))
    if h == 'KExpr.bvar':
        return ('bvar', natlit(sx[1]))
    if h == 'KExpr.sort':
        return ('sort', sx_str(sx_map_atoms(sx[1], rename)))
    if h == 'KExpr.const':
        return ('const', rename(sx[1]), sx_str(sx_map_atoms(sx[2], rename)))
    raise ValueError('unsupported node %s' % h)


def parse(s):
    return conv(parse_sx(s))


# ---------------------------------------------------------------- terms
NIL_LV = '(ListType.nil Level)'
LV1 = '(ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))'


def C(name, lv=NIL_LV):
    return ('const', 'kcre_name_@@%s@@' % name, lv)


def app(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = ('app', t, x)
    return t


def lam(a, b):
    return ('lam', a, b)


def pi(a, b):
    return ('pi', a, b)


def bv(i):
    return ('bvar', i)


def lit(payload):
    return ('lit', payload)


def blit(payload):
    return ('blit', payload)


def ref(name, term):
    return ('ref', name, term)


def lift(t, c, k):
    tag = t[0]
    if tag == 'bvar':
        return ('bvar', t[1] + k) if t[1] >= c else t
    if tag == 'app':
        return ('app', lift(t[1], c, k), lift(t[2], c, k))
    if tag in ('lam', 'pi'):
        return (tag, lift(t[1], c, k), lift(t[2], c + 1, k))
    if tag == 'let':
        return ('let', lift(t[1], c, k), lift(t[2], c, k), lift(t[3], c + 1, k))
    if tag == 'proj':
        return ('proj', t[1], t[2], lift(t[3], c, k))
    return t  # sort, const, lit, ref (closed)


def inst(body, val, depth=0):
    tag = body[0]
    if tag == 'bvar':
        i = body[1]
        if i < depth:
            return body
        if i == depth:
            return lift(val, 0, depth)
        return ('bvar', i - 1)
    if tag == 'app':
        return ('app', inst(body[1], val, depth), inst(body[2], val, depth))
    if tag in ('lam', 'pi'):
        return (tag, inst(body[1], val, depth), inst(body[2], val, depth + 1))
    if tag == 'let':
        return ('let', inst(body[1], val, depth), inst(body[2], val, depth), inst(body[3], val, depth + 1))
    if tag == 'proj':
        return ('proj', body[1], body[2], inst(body[3], val, depth))
    return body


def unref(t):
    while t[0] == 'ref':
        t = t[2]
    return t


def spine(t):
    args = []
    while t[0] == 'app':
        args.append(t[2])
        t = t[1]
    return t, args[::-1]


NAMED = {}


def name_term(name, t):
    NAMED[unref_deep(t)] = name
    return ref(name, t)


def pr(t):
    if t[0] != 'ref' and t[0] not in ('bvar', 'sort', 'const', 'lit'):
        n = NAMED.get(unref_deep(t)) if NAMED else None
        if n is not None:
            return n
    tag = t[0]
    if tag == 'bvar':
        return '(KExpr.bvar kcre_nat_%d)' % t[1]
    if tag == 'app':
        return '(KExpr.app %s %s)' % (pr(t[1]), pr(t[2]))
    if tag == 'lam':
        return '(KExpr.lam %s %s)' % (pr(t[1]), pr(t[2]))
    if tag == 'pi':
        return '(KExpr.pi %s %s)' % (pr(t[1]), pr(t[2]))
    if tag == 'let':
        return '(KExpr.let_ %s %s %s)' % (pr(t[1]), pr(t[2]), pr(t[3]))
    if tag == 'sort':
        return '(KExpr.sort %s)' % t[1]
    if tag == 'proj':
        return '(KExpr.proj %s kcre_nat_%d %s)' % (t[1], t[2], pr(t[3]))
    if tag == 'const':
        return '(KExpr.const %s %s)' % (t[1], t[2])
    if tag == 'lit':
        return '(literal_nat %s)' % t[1]
    if tag == 'blit':
        return '(accepts_tc_bool_lit %s)' % t[1]
    if tag == 'ref':
        return t[1]
    raise ValueError(tag)


def eq(a, b):
    return unref_deep(a) == unref_deep(b)


def unref_deep(t):
    tag = t[0]
    if tag == 'ref':
        return unref_deep(t[2])
    if tag == 'app':
        return ('app', unref_deep(t[1]), unref_deep(t[2]))
    if tag in ('lam', 'pi'):
        return (tag, unref_deep(t[1]), unref_deep(t[2]))
    if tag == 'let':
        return ('let', unref_deep(t[1]), unref_deep(t[2]), unref_deep(t[3]))
    if tag == 'proj':
        return ('proj', t[1], t[2], unref_deep(t[3]))
    return t


def inst_levels(t, param_atom, level_str):
    """instLevels for a single-parameter signature (the Nat.rec / Bool.rec case)."""
    old = '(Level.param %s)' % param_atom
    tag = t[0]
    if tag == 'sort':
        return ('sort', t[1].replace(old, level_str))
    if tag == 'const':
        return ('const', t[1], t[2].replace(old, level_str))
    if tag == 'app':
        return ('app', inst_levels(t[1], param_atom, level_str), inst_levels(t[2], param_atom, level_str))
    if tag in ('lam', 'pi'):
        return (tag, inst_levels(t[1], param_atom, level_str), inst_levels(t[2], param_atom, level_str))
    if tag == 'let':
        return ('let',) + tuple(inst_levels(x, param_atom, level_str) for x in t[1:])
    if tag == 'proj':
        return ('proj', t[1], t[2], inst_levels(t[3], param_atom, level_str))
    return t


# ---------------------------------------------------------------- proofs
class Conv:
    """A KernelAcceptsTcIn R tenv Bool.false G lhs rhs proof."""

    def __init__(self, lhs, rhs, proof):
        self.lhs, self.rhs, self.proof = lhs, rhs, proof

    def ty(self):
        return 'KernelAcceptsTcIn R tenv Bool.false G %s %s' % (pr(self.lhs), pr(self.rhs))


def refl(t):
    return Conv(t, t, '(KernelAcceptsTcIn.cdp R tenv G %s %s (DefEqCDPIn.refl R %s))' % (pr(t), pr(t), pr(t)))


def symm(c):
    return Conv(c.rhs, c.lhs, '(KernelAcceptsTcIn.symm R tenv G %s %s %s)' % (pr(c.lhs), pr(c.rhs), c.proof))


def trans(c1, c2, check=True):
    if check and not eq(c1.rhs, c2.lhs):
        raise ValueError('trans mismatch:\n  %s\n  %s' % (pr(c1.rhs), pr(c2.lhs)))
    return Conv(c1.lhs, c2.rhs, '(KernelAcceptsTcIn.trans R tenv G %s %s %s %s %s)' % (
        pr(c1.lhs), pr(c1.rhs), pr(c2.rhs), c1.proof, c2.proof))


def chain(cs):
    """balanced trans tree (keeps parser nesting shallow)"""
    cs = [c for c in cs if c is not None]
    if len(cs) == 1:
        return cs[0]
    mid = len(cs) // 2
    return trans(chain(cs[:mid]), chain(cs[mid:]))


def app_l(cf, a):
    return Conv(('app', cf.lhs, a), ('app', cf.rhs, a),
                '(accepts_tc_app_l R tenv G %s %s %s %s)' % (pr(cf.lhs), pr(cf.rhs), pr(a), cf.proof))


def app_r(f, ca):
    return Conv(('app', f, ca.lhs), ('app', f, ca.rhs),
                '(accepts_tc_app_r R tenv G %s %s %s %s)' % (pr(f), pr(ca.lhs), pr(ca.rhs), ca.proof))


def appcong(cf, ca):
    return Conv(('app', cf.lhs, ca.lhs), ('app', cf.rhs, ca.rhs),
                '(KernelAcceptsTcIn.app_cong R tenv G %s %s %s %s %s %s)' % (
                    pr(cf.lhs), pr(cf.rhs), pr(ca.lhs), pr(ca.rhs), cf.proof, ca.proof))


def at_arg(term, idx, c):
    """rewrite the idx-th spine argument of term by conversion c (others refl)."""
    head, args = spine(unref(term)) if term[0] == 'ref' else spine(term)
    assert eq(args[idx], c.lhs), (pr(args[idx]), pr(c.lhs))
    f = app(head, *args[:idx])
    cur = app_r(f, c)
    for a in args[idx + 1:]:
        cur = app_l(cur, a)
    return cur


def lit_zero():
    return Conv(lit('Nat.zero'), C('Nat.zero'), '(KernelAcceptsTcIn.lit_zero R tenv G)')


def lit_succ(n):
    """literal (succ n) == Nat.succ (literal n)"""
    return Conv(lit('(Nat.succ %s)' % n), app(C('Nat.succ'), lit(n)),
                '(KernelAcceptsTcIn.lit_succ R tenv G %s)' % n)


def raw(e, e2, par):
    return Conv(e, e2, '(KernelAcceptsTcIn.cdp R tenv G %s %s (DefEqCDPIn.raw R %s %s %s))' % (
        pr(e), pr(e2), pr(e), pr(e2), par))


def par_refl(t):
    return '(par_reduces_cdp.refl R %s)' % pr(t)


def beta_par(e):
    """one head beta step on e's spine: (e2, par proof)"""
    e = unref(e)
    assert e[0] == 'app', pr(e)
    f, a = unref(e[1]), e[2]
    if f[0] == 'lam':
        A, b = f[1], f[2]
        e2 = inst(b, a)
        return e2, '(par_reduces_cdp.beta R %s %s %s %s %s %s %s %s %s)' % (
            pr(A), pr(A), pr(b), pr(b), pr(a), pr(a), par_refl(A), par_refl(b), par_refl(a))
    f2, pf = beta_par(f)
    return ('app', f2, a), '(par_reduces_cdp.app R %s %s %s %s %s %s)' % (
        pr(e[1]), pr(f2), pr(a), pr(a), pf, par_refl(a))


def beta(e):
    e = unref(e)
    assert e[0] == 'app', pr(e)
    f, a = unref(e[1]), e[2]
    if f[0] == 'lam':
        e2 = inst(f[2], a)
        return Conv(e, e2, '(accepts_tc_beta R tenv G %s %s %s)' % (pr(f[1]), pr(f[2]), pr(a)))
    return app_l(beta(e[1]), a)


def betas(e, n):
    cs = []
    for _ in range(n):
        c = beta(e)
        cs.append(c)
        e = c.rhs
    return chain(cs)


def delta(e, name, body, hyp):
    """unfold the head constant `name` (value premise hyp)"""
    head, args = spine(e)
    assert head[0] == 'const' and head[1] == 'kcre_name_@@%s@@' % name
    e2 = app(body, *args)
    return Conv(e, e2, '(accepts_tc_delta R tenv G %s %s %s (Eq.refl (OptionType Name) (OptionType.some Name %s)) %s)' % (
        pr(e), head[1], pr(body), head[1], hyp))


class Rec:
    """A recursor with its canonical meta atom and rules (ctor name -> (nfields, rhs AST))."""

    def __init__(self, name, meta_atom, rules, param_atom, hmeta, hrules):
        self.name, self.meta_atom, self.rules = name, meta_atom, rules
        self.param_atom = param_atom
        self.hmeta, self.hrules = hmeta, hrules  # premise names
        self.prefix = None  # set by caller: params+motives+minors
        self.rule_consts = {}  # ctor -> spec constant name of the RecRule


def iota(e, rec, level_str, rule_const_names):
    """one iota step at the root of e (major must be ctor-headed)."""
    head, args = spine(e)
    npre = rec.prefix
    major = args[npre]
    mh, margs = spine(major)
    assert mh[0] == 'const', pr(major)
    cname = mh[1]
    ctor = re.fullmatch(r'kcre_name_@@(.*)@@', cname).group(1)
    nf, rhs = rec.rules[ctor]
    rhs_i = inst_levels(rhs, rec.param_atom, level_str)
    fields = margs[len(margs) - nf:] if nf else []
    r = app(rhs_i, *(args[:npre] + fields + args[npre + 1:]))
    proof = ('(accepts_tc_iota R tenv G %s %s %s %s %s %s %s '
             '(Eq.refl (OptionType Name) (OptionType.some Name %s)) %s '
             '(Eq.refl (OptionType KExpr) (OptionType.some KExpr %s)) '
             '(Eq.refl (OptionType Name) (OptionType.some Name %s)) %s '
             '(Eq.refl (OptionType KExpr) (OptionType.some KExpr %s)))') % (
        pr(e), head[1], rec.meta_atom, pr(major), cname, rule_const_names[ctor], pr(r),
        head[1], rec.hmeta, pr(major), cname, rec.hrules[ctor], pr(r))
    return Conv(e, r, proof)


def retype_rhs(c, new_rhs):
    """same proof, rhs restated up to kernel definitional equality"""
    return Conv(c.lhs, new_rhs, c.proof)


def retype_lhs(c, new_lhs):
    return Conv(new_lhs, c.rhs, c.proof)
