"""Extract canonical reflected data (rules, bodies) from kernel_core_red_env.defs.txt."""
from kx import GEN, parse_sx, conv, sx_str, sx_map_atoms, rename, parse, pr

DEFS = open(GEN + 'kernel_core_red_env.defs.txt').read().split('\n')
ENV_LINE = [l for l in DEFS if l.startswith('def kernel_core_red_env ')][0]
ENV_SX = parse_sx('(' + ENV_LINE.split(':=', 1)[1].strip() + ')')


def find_all(sx, pred, out):
    if isinstance(sx, list):
        if pred(sx):
            out.append(sx)
        for x in sx:
            find_all(x, pred, out)
    return out


def rec_entry(tag):
    """(meta atom, [(ctor atom, nfields atom, rhs sx)]) for RecEnv.addRec ... kcre_name_<tag>"""
    hits = find_all(ENV_SX, lambda s: len(s) == 5 and s[0] == 'RecEnv.addRec' and s[2] == 'kcre_name_%d' % tag, [])
    assert len(hits) == 1, len(hits)
    _, _, _, meta, rules = hits[0]
    out = []
    while rules != 'RecRules.nil':
        assert rules[0] == 'RecRules.cons'
        rule = rules[1]
        assert rule[0] == 'RecRule.mk'
        out.append((rule[1], rule[2], rule[3]))
        rules = rules[2]
    return meta, out


def def_entry(tag):
    hits = find_all(ENV_SX, lambda s: len(s) == 4 and s[0] == 'DefEnv.addDef' and s[2] == 'kcre_name_%d' % tag, [])
    assert len(hits) == 1, len(hits)
    sig = hits[0][3]
    assert sig[0] == 'KDefSig.mk'
    return sig[1], sig[2]  # KConstSig, value


def natv(atom):
    return int(atom.split('_')[-1])


def rule_rhs(rec_tag, ctor_name):
    from kx import NAME2TAG
    meta, rules = rec_entry(rec_tag)
    for c, nf, rhs in rules:
        if c == 'kcre_name_%d' % NAME2TAG[ctor_name]:
            return natv(nf), conv(rhs)
    raise KeyError(ctor_name)


def body(name):
    from kx import NAME2TAG
    sig, val = def_entry(NAME2TAG[name])
    return conv(val)
