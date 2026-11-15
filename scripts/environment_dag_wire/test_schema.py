#!/usr/bin/env python3
"""Focused static schema/generator controls, never Rust/runtime proof credit."""
import copy
import importlib.util
import json
from pathlib import Path
import re
import unittest

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('fixed_wire_generator',HERE/'generate.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
SCHEMA=json.loads(g.SCHEMA.read_text())
g.NAMES={row['name'] for row in SCHEMA['declarations']}

class FixedSchema(unittest.TestCase):
    def test_complete_recursive_inventory(self):
        self.assertEqual(len(g.NAMES),43)
        self.assertEqual(sum(row['kind']=='enum' for row in SCHEMA['declarations']),24)
        self.assertEqual(sum(len(row['items']) for row in SCHEMA['declarations'] if row['kind']=='enum'),116)
        self.assertEqual(len(g.SKIP),7)

    def test_all_current_and_legacy_fields_are_explicit(self):
        new=SCHEMA['environment_fields'];old=SCHEMA['legacy_3fa_fields']
        self.assertEqual((len(new),len(old)),(566,563))
        current=[f for f in new if f['serialized']]
        previous=[f for f in old if f['serialized']]
        self.assertEqual((len(current),len(previous)),(555,554))
        self.assertEqual(sum(f['type']=='bool' for f in current),491)
        self.assertEqual(current[519]['name'],'lean_level_profile')
        self.assertEqual([f for f in current if f['name']!='lean_level_profile'],previous)
        # Transient fields carry no wire bytes; neither adds serialized state.
        self.assertEqual({f['name'] for f in new if not f['serialized']},
                         {f['name'] for f in old if not f['serialized']}|{'matcher_info','simp_cache_identity'})

    def test_metadata_is_an_ordered_sequence_not_a_map(self):
        self.assertEqual(g.wire_type('MDataMap'),'Vec<(WName, WMDataValue)>')
        expr=next(r for r in SCHEMA['declarations'] if r['name']=='ExprKind')
        out=g.enum_body(expr)
        self.assertIn('MData(Vec<(WName, WMDataValue)>, Ref)',out)
        self.assertNotIn('MData(Map<',out)

    def test_nested_shapes_have_no_unknown_or_live_wire_payload(self):
        generated=g.generate(SCHEMA)
        known={'Map','Set','Vec','Option','Box','String','Ref','Unit','bool','u8','u32','u64','usize'}|{'W'+n for n in g.NAMES}
        for row in SCHEMA['declarations']:
            if row['name'] in g.SKIP:continue
            entries=(g.fields(','.join(row['items'])) if row['kind']=='struct' else [(f,t) for entry in row['items'] for _,_,fs in [g.variant(entry)] for f,t in fs])
            for _,source in entries:
                tokens=set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*',g.wire_type(source)))
                self.assertFalse(tokens-known,(row['name'],tokens-known))
        for text in generated.values():
            self.assertNotRegex(text,r'\b(?:Serialize|Deserialize)\b')
            self.assertNotRegex(text,r'\b(?:bincode|serde)::')

    def test_generator_never_rescans_live_schema(self):
        source=(HERE/'generate.py').read_text()
        self.assertNotIn('subprocess',source)
        self.assertNotIn('include_str!',source)
        self.assertNotIn('serde_json::to_value',source)
        self.assertIn('SCHEMA.read_text()',source)

    def test_generated_sources_match_frozen_tokens(self):
        for relative,text in g.generate(SCHEMA).items():
            self.assertEqual(g.tokens((g.OUT/relative).read_text()),g.tokens(text),relative)

    def test_semantic_mutation_is_detected_but_formatting_is_not(self):
        one='fn f(){Err(error("unknown Name tag"))}'
        self.assertEqual(g.tokens(one),g.tokens('fn f() { Err(error("unknown Name tag")) }'))
        self.assertNotEqual(g.tokens(one),g.tokens(one.replace('Name tag','Name  tag')))
        self.assertNotEqual(g.tokens(one),g.tokens(one.replace('Err','Ok')))
        arm='0 => Ok(Self::Case { first: a, second: b })'
        block='0 => { Ok(Self::Case { first: a, second: b, }) }'
        self.assertEqual(g.tokens(arm),g.tokens(block))
        self.assertNotEqual(g.tokens(arm),g.tokens(block.replace('first: a, second: b','second: b, first: a')))
        self.assertNotEqual(g.tokens(arm),g.tokens(block.replace('{ Ok','{ opaque(); Ok')))

    def test_wrong_field_census_is_not_silently_absorbed(self):
        altered=copy.deepcopy(SCHEMA)
        altered['environment_fields'].append({'name':'new_semantics','type':'bool','serialized':True,'attributes':[]})
        with self.assertRaises(AssertionError):g.generate(altered)

    def test_persisted_tags_field_order_types_and_collection_kind_are_not_formatting(self):
        original=g.generate(SCHEMA)
        expr='types/expr_kind.rs'
        changed=original[expr].replace('0 => { Ok(Self::BVar','1 => { Ok(Self::BVar',1)
        self.assertNotEqual(g.tokens(changed),g.tokens(original[expr]))
        changed=original[expr].replace('MData(Vec<(WName, WMDataValue)>','MData(Map<WName, WMDataValue>',1)
        self.assertNotEqual(g.tokens(changed),g.tokens(original[expr]))
        changed=original[expr].replace('BVar(u32)','BVar(u64)',1)
        self.assertNotEqual(g.tokens(changed),g.tokens(original[expr]))
        schema=copy.deepcopy(SCHEMA)
        fieldlist=schema['environment_fields']
        fieldlist[0],fieldlist[1]=fieldlist[1],fieldlist[0]
        self.assertNotEqual(g.tokens(g.generate(schema)['environment_fields.rs']),g.tokens(original['environment_fields.rs']))
        schema=copy.deepcopy(SCHEMA)
        row=next(r for r in schema['declarations'] if r['name']=='ConstantKind')
        row['items'][0],row['items'][1]=row['items'][1],row['items'][0]
        self.assertNotEqual(g.tokens(g.generate(schema)['types/constant_kind.rs']),g.tokens(original['types/constant_kind.rs']))

    def test_context_bindings_cannot_be_shadowed_by_any_semantic_field(self):
        labels=['r','p','w','wire','__wire_field_0']
        row={'name':'Collision','live_path':'crate::Collision','kind':'enum',
             'items':['Case { '+', '.join(n+': u32' for n in labels)+' }']}
        text=g.enum_body(row)
        for i,name in enumerate(labels):
            self.assertIn(name+': __wire_field_'+str(i),text)
            self.assertIn('FromWire::from_wire(__wire_field_'+str(i)+', r)',text)
        self.assertNotIn('from_wire(r, r)',text)
        self.assertNotIn('r.to_wire(p)',text)
        row={'name':'Collision','live_path':'crate::Collision','kind':'struct',
             'items':['pub '+n+': u32' for n in labels]}
        text=g.struct_body(row)
        for i,name in enumerate(labels):self.assertIn(name+': __wire_field_'+str(i),text)
        self.assertNotIn('from_wire(r, r)',text)
        # Environment fields/transients use the same distinct-label policy.
        schema=copy.deepcopy(SCHEMA)
        target=next(f for f in schema['environment_fields'] if f['name']=='mode')
        target['name']='p'
        self.assertIn('p: WCleanMode => __wire_env_0',g.generate(schema)['environment_fields.rs'])

    def test_level_profile_import_uses_existing_public_reexport(self):
        row=next(r for r in SCHEMA['declarations'] if r['name']=='LeanLevelProfile')
        self.assertEqual(g.source_path(row),'crate::level::LeanLevelProfile')
        self.assertNotIn('level::lean_kernel',g.enum_body(row))

if __name__=='__main__':unittest.main()
