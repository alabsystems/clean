#!/usr/bin/env python3
"""Materialize the fixed recursive wire schema, never infer live serde fields."""
import argparse
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
SCHEMA=ROOT/'data/environment_dag_wire/schema_v2.json'
OUT=ROOT/'crates/clean-kernel/src/env/dag_serialization'
SKIP={'Environment','Name','NameInner','Expr','Level','FVarId','EnvExtensionStates'}
VIS='pub(in crate::env::dag_serialization)'

def clean(s):
    return re.sub(r'#\[[^]]*\]','',s).strip()

def split(s):
    out=[];start=0;stack=[]
    for i,c in enumerate(s):
        if c in '(<[{':stack.append(c)
        elif c in ')>]}':stack.pop()
        elif c==',' and not stack:
            if s[start:i].strip():out.append(s[start:i].strip())
            start=i+1
    if s[start:].strip():out.append(s[start:].strip())
    return out

def fields(s):
    result=[]
    for f in split(s):
        m=re.fullmatch(r'(?:pub(?:\([^)]*\))?\s+)?(\w+)\s*:\s*(.*)',clean(f))
        if not m:raise ValueError(f)
        result.append((m[1],m[2]))
    return result

def source_path(row):
    return row['live_path']

def binding_fields(fs):
    # Semantic field labels NEVER become local identifiers. In particular
    # CubicalCoe.r cannot shadow the mutable restoration context named r.
    return [(field,ty,f'__wire_field_{i}') for i,(field,ty) in enumerate(fs)]

def case_pattern(owner,name,kind,fs):
    pat=owner+'::'+name
    if kind=='tuple':pat+='('+', '.join(b for _,_,b in binding_fields(fs))+')'
    elif kind=='named':pat+=' { '+', '.join(f'{f}: {b}' for f,_,b in binding_fields(fs))+' }'
    return pat

def wire_type(t):
    t=clean(t)
    t=t.replace('MDataMap','Vec<(WName, WMDataValue)>')
    t=t.replace('Arc<Expr>','Ref').replace('Arc<Name>','Box<WName>').replace('Arc<str>','String')
    t=t.replace('LevelArc','Box<WLevel>').replace('LevelVec','Vec<WLevel>')
    t=t.replace('hashbrown::HashSet','Set').replace('HashMap','Map')
    t=t.replace('crate::level::LeanLevelProfile','WLeanLevelProfile').replace('crate::mode::CleanMode','WCleanMode')
    t=t.replace('persistent_ext::EnvExtensionStates','Unit')
    for name in NAMES:
        if name in ('Environment','NameInner','EnvExtensionStates'):continue
        target='Ref' if name=='Expr' else 'W'+name
        t=re.sub(r'\b'+name+r'\b',target,t)
    return t

def variant(entry):
    s=clean(entry)
    m=re.match(r'(\w+)',s);name=m[1];rest=s[m.end():].strip()
    if not rest or rest.startswith('='):return name,'unit',[]
    if rest.startswith('('):return name,'tuple',[(f'v{i}',t) for i,t in enumerate(split(rest[1:-1]))]
    if rest.startswith('{'):return name,'named',fields(rest[1:-1])
    raise ValueError(s)

def enum_body(row):
    name=row['name'];wire='W'+name;live='S'+name
    cases=[variant(x) for x in row['items']]
    lines=[f'use {source_path(row)} as {live};', '#[derive(Debug, PartialEq, Eq)]',f'{VIS} enum {wire} {{']
    for n,k,fs in cases:
        if k=='unit':lines.append(f'    {n},')
        elif k=='tuple':lines.append(f'    {n}('+', '.join(wire_type(t) for _,t in fs)+'),')
        else:lines.append(f'    {n} {{ '+', '.join(f'{f}: {wire_type(t)}' for f,t in fs)+' },')
    lines+=['}',f'impl Wire for {wire} {{',"    fn read(r: &mut Decoder<'_>) -> Result<Self> {",'        match r.u32()? {']
    for tag,(n,k,fs) in enumerate(cases):
        args=[f'<{wire_type(t)} as Wire>::read(r)?' for _,t in fs]
        value='Self::'+n
        if k=='tuple':value+='('+', '.join(args)+')'
        elif k=='named':value+=' { '+', '.join(f'{f}: {v}' for (f,_),v in zip(fs,args))+' }'
        lines.append(f'            {tag} => {{ Ok({value}) }}')
    lines+=['            _ => Err(error("unknown '+wire+' tag")),','        }','    }','    fn write(&self, w: &mut Encoder) -> Result<()> {','        match self {']
    for tag,(n,k,fs) in enumerate(cases):
        pat=case_pattern('Self',n,k,fs)
        seq=' '.join(f'{b}.write(w)?;' for _,_,b in binding_fields(fs))
        lines.append(f'            {pat} => {{ w.u32({tag})?; {seq} Ok(()) }}')
    pure=all(not fs for _,_,fs in cases)
    pn='_p' if pure else 'p'
    rn='_r' if pure else 'r'
    lines+=['        }','    }','}',f'impl ToWire for {live} {{',f'    type Wire = {wire};',f'    fn to_wire(&self, {pn}: &mut Projection) -> Result<Self::Wire> {{','        match self {']
    for n,k,fs in cases:
        pat=case_pattern(live,n,k,fs)
        args=[f'{b}.to_wire(p)?' for _,_,b in binding_fields(fs)];value=wire+'::'+n
        if k=='tuple':value+='('+', '.join(args)+')'
        elif k=='named':value+=' { '+', '.join(f'{f}: {v}' for (f,_),v in zip(fs,args))+' }'
        lines.append(f'            {pat} => {{ Ok({value}) }}')
    lines+=['        }','    }','}',f'impl FromWire<{wire}> for {live} {{',f'    fn from_wire(wire: {wire}, {rn}: &mut Restoration) -> Result<Self> {{','        match wire {']
    for n,k,fs in cases:
        pat=case_pattern(wire,n,k,fs)
        args=[f'FromWire::from_wire({b}, r)?' for _,_,b in binding_fields(fs)];value='Self::'+n
        if k=='tuple':value+='('+', '.join(args)+')'
        elif k=='named':value+=' { '+', '.join(f'{f}: {v}' for (f,_),v in zip(fs,args))+' }'
        lines.append(f'            {pat} => {{ Ok({value}) }}')
    lines+=['        }','    }','}']
    return '\n'.join(lines)+'\n'

def struct_body(row):
    name=row['name'];wire='W'+name;live='S'+name
    fs=fields(','.join(row['items']))
    lines=[f'use {source_path(row)} as {live};','#[derive(Debug, PartialEq, Eq)]',f'{VIS} struct {wire} {{']
    lines += [f'    {VIS} {f}: {wire_type(t)},' for f,t in fs]
    lines += ['}',f'impl Wire for {wire} {{',"    fn read(r: &mut Decoder<'_>) -> Result<Self> {",'        Ok(Self {']
    lines += [f'            {f}: <{wire_type(t)} as Wire>::read(r)?,' for f,t in fs]
    lines += ['        })','    }','    fn write(&self, w: &mut Encoder) -> Result<()> {']
    lines += [f'        self.{f}.write(w)?;' for f,_ in fs]
    lines += ['        Ok(())','    }','}',f'impl ToWire for {live} {{',f'    type Wire = {wire};','    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {']
    lines += [f'        let {live} {{ '+', '.join(f'{f}: {b}' for f,_,b in binding_fields(fs))+' } = self;',f'        Ok({wire} {{']
    lines += [f'            {f}: {b}.to_wire(p)?,' for f,_,b in binding_fields(fs)]
    lines += ['        })','    }','}',f'impl FromWire<{wire}> for {live} {{',f'    fn from_wire(wire: {wire}, r: &mut Restoration) -> Result<Self> {{',f'        let {wire} {{ '+', '.join(f'{f}: {b}' for f,_,b in binding_fields(fs))+' } = wire;','        Ok(Self {']
    lines += [f'            {f}: FromWire::from_wire({b}, r)?,' for f,_,b in binding_fields(fs)]
    lines += ['        })','    }','}']
    return '\n'.join(lines)+'\n'

def generate(schema):
    results={};modules=[]
    header='// Copyright 2026 Andrew Yates | Apache-2.0\n// Generated from the frozen schema_v2.json; do not infer live serde.\nuse super::*;\n'
    for row in schema['declarations']:
        if row['name'] in SKIP:continue
        name=re.sub(r'(?<!^)(?=[A-Z])','_',row['name']).lower()
        body=enum_body(row) if row['kind']=='enum' else struct_body(row)
        results['types/'+name+'.rs']=header+body
        modules += [f'mod {name};',f'pub(super) use {name}::W{row["name"]};']
    results['types/mod.rs']='// Copyright 2026 Andrew Yates | Apache-2.0\nuse super::{containers::*, error, graph::{Projection, Ref, Restoration}, primitive::*, syntax::*};\n'+'\n'.join(modules)+'\n'
    fs=schema['environment_fields']; before=[];after=[];skipped=[];seen=False
    for i,f in enumerate(fs):
        binding=f'__wire_env_{i}'
        if not f['serialized']:skipped.append((f['name'],binding));continue
        if f['name']=='lean_level_profile':seen=True;continue
        (after if seen else before).append((f['name'],wire_type(f['type']),binding))
    assert len(before)==519 and len(before)+len(after)==554 and len(skipped)==11
    lines=['// Copyright 2026 Andrew Yates | Apache-2.0','// Fixed schema data; the macro exhaustively matches the live Environment.','environment_schema! {','    before {']
    for group in (before,after):
        for i in range(0,len(group),2):lines.append('        '+' '.join(f'{n}: {t} => {b},' for n,t,b in group[i:i+2]))
        if group is before:lines+=['    }','    after {']
    lines += ['    }','    transient { '+', '.join(f'{n} => {b}' for n,b in skipped)+' }','}']
    results['environment_fields.rs']='\n'.join(lines)+'\n'
    return results

def main():
    global NAMES
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    schema=json.loads(SCHEMA.read_text());NAMES={x['name'] for x in schema['declarations']}
    assert schema['wire_schema']==2 and len(NAMES)==43
    results=generate(schema)
    for relative,text in results.items():
        path=OUT/relative
        if args.check:
            if not path.exists() or tokens(path.read_text())!=tokens(text):raise SystemExit('stale generated wire file: '+relative)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    print(f'fixed wire schema: {len(results)} generated files, {len(NAMES)} source representations')

def tokens(text):
    # Generated files have only the two fixed line comments and ordinary
    # quoted error strings; keep string bytes exact while tolerating Trustfmt.
    text=re.sub(r'(?m)^\s*//[^\n]*','',text)
    result=re.findall(r'"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_]*|[0-9]+|::|->|=>|[^\s]',text)
    # The fixed generated grammar contains structs, enum payloads and function
    # arguments, but no anonymous one-tuples. Trustfmt's optional trailing
    # argument/field comma changes no represented type/value in that grammar.
    result=[t for i,t in enumerate(result) if not(t==',' and i+1<len(result) and result[i+1] in (')','}','>'))]
    # Trustfmt adds/removes an arm block around a sole Result-constructor
    # tail expression according to width. Strip ONLY that outer block, not
    # structs, payload blocks, statements, fields, tags, types or their order.
    out=[];i=0
    while i<len(result):
        if result[i]=='=>':
            start=i+1
            block=start<len(result) and result[start]=='{'
            inner=start+1 if block else start
            if inner+1<len(result) and result[inner] in ('Ok','Err') and result[inner+1]=='(':
                depth=1;end=inner+2
                while end<len(result) and depth:
                    if result[end]=='(':depth+=1
                    elif result[end]==')':depth-=1
                    end+=1
                valid=depth==0 and end<len(result)
                if block:valid=valid and result[end]=='}'
                else:valid=valid and result[end] in (',','}')
                if valid:
                    out.append('=>');out.extend(result[inner:end])
                    if block:end+=1
                    if end<len(result) and result[end]==',':end+=1
                    i=end;continue
        out.append(result[i]);i+=1
    return out

if __name__=='__main__':main()
