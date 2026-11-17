// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Raw pointer mutations of a checked declaration exported by the normal
//! exporter, consumed through the production checked graph loader.

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Declaration, Environment, Expr, Name};
use clean_olean::header::{HEADER_SIZE, VERSION};
use clean_olean::region::CompactedRegion;
use clean_olean::{
    default_fn_binder_idx, load_modules_with_deps_checked, parse_header, type_binder_names,
    DefaultFnBinderState, ImportError, OleanExporter,
};
use std::time::Instant;

#[derive(Clone, Copy)]
enum Lane {
    Type,
    Value,
    Default,
}

struct Fixture {
    bytes: Vec<u8>,
    base: u64,
    slot: usize,
    name: &'static str,
    prefix: u64,
    full_name: u64,
}

impl Fixture {
    fn new(lane: Lane, type_: Expr, value: Option<Expr>) -> Self {
        let name = if matches!(lane, Lane::Default) {
            "Root.subject._default"
        } else {
            "Root.subject"
        };
        let mut env = Environment::default();
        let declaration = match value {
            Some(value) => Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            },
            None => Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
            },
        };
        env.add_decl(declaration)
            .expect("checked original declaration");
        let bytes = OleanExporter::export_with_env(
            &env,
            &[],
            &[],
            "0000000000000000000000000000000000000000",
        )
        .expect("normal export");
        let header = parse_header(&bytes).unwrap();
        assert_eq!(
            header.version, VERSION,
            "normal exporter uses its legacy header"
        );
        let base = header.base_addr;
        let r = CompactedRegion::new(&bytes, base);
        let root = r
            .ptr_to_offset(r.read_u64_at(HEADER_SIZE).unwrap())
            .unwrap();
        let constants = r.ptr_to_offset(r.read_u64_at(root + 24).unwrap()).unwrap();
        assert_eq!(r.read_u64_at(constants + 8).unwrap(), 1);
        let info = r
            .ptr_to_offset(r.read_u64_at(constants + 24).unwrap())
            .unwrap();
        let val = r.ptr_to_offset(r.read_u64_at(info + 8).unwrap()).unwrap();
        let cv = r.ptr_to_offset(r.read_u64_at(val + 8).unwrap()).unwrap();
        let full_name = r.read_u64_at(cv + 8).unwrap();
        let name_offset = r.ptr_to_offset(full_name).unwrap();
        let prefix = r.read_u64_at(name_offset + 8).unwrap();
        let slot = if matches!(lane, Lane::Type) {
            cv + 24
        } else {
            val + 16
        };
        Self {
            bytes,
            base,
            slot,
            name,
            prefix,
            full_name,
        }
    }

    fn pointer(&self) -> u64 {
        u64::from_le_bytes(self.bytes[self.slot..self.slot + 8].try_into().unwrap())
    }

    fn word(&mut self, offset: usize, value: u64) {
        self.bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }

    fn mdata(&mut self, inner: u64) -> u64 {
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        let pointer = self.base + self.bytes.len() as u64;
        // Existing Clean legacy Expr header, empty KVMap, expression child.
        self.bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, 2, 10]);
        self.bytes.extend_from_slice(&1u64.to_le_bytes());
        self.bytes.extend_from_slice(&inner.to_le_bytes());
        pointer
    }

    fn lambda_with_info(&mut self, original: u64, body: u64, info: u8) -> u64 {
        let offset = (original - self.base) as usize;
        assert_eq!(&self.bytes[offset + 6..offset + 8], &[3, 6]);
        // Preserve the checked lambda's pointer fields while independently
        // exercising the raw Expr.Data/BinderInfo layout consumed by import.
        let mut fields = self.bytes[offset..offset + 32].to_vec();
        fields[24..32].copy_from_slice(&body.to_le_bytes());
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        let pointer = self.base + self.bytes.len() as u64;
        self.bytes.extend_from_slice(&fields);
        // A distinct cache byte makes a mistaken cache-as-BinderInfo read fail.
        self.bytes.extend_from_slice(&3u64.to_le_bytes());
        self.bytes.push(info);
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        pointer
    }

    fn point_at(&mut self, pointer: u64) {
        self.word(self.slot, pointer);
    }

    fn load(&self) -> Result<Environment, ImportError> {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("Root.olean"), &self.bytes).unwrap();
        let mut env = Environment::default();
        load_modules_with_deps_checked(
            &mut env,
            &["Root".into()],
            &[dir.path().into()],
            &mut |_, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        )?;
        Ok(env)
    }
}

fn simple(lane: Lane) -> Fixture {
    Fixture::new(
        lane,
        if matches!(lane, Lane::Type) {
            Expr::prop()
        } else {
            Expr::type_()
        },
        (!matches!(lane, Lane::Type)).then(Expr::prop),
    )
}

fn cycle(lane: Lane, two_nodes: bool) {
    let mut f = simple(lane);
    let first = f.mdata(1);
    let next = if two_nodes { f.mdata(first) } else { first };
    f.word((first - f.base) as usize + 16, next);
    f.point_at(first);
    let error = match f.load() {
        Err(error) => error,
        Ok(_) => panic!("a cyclic raw spine was accepted"),
    };
    assert!(
        matches!(error, ImportError::ResourceLimit { operation, reason }
        if operation.contains(f.name) && reason.contains("cyclic expression spine"))
    );
}

#[test]
fn type_mdata_self_cycle_refuses() {
    cycle(Lane::Type, false);
}
#[test]
fn type_mdata_two_node_cycle_refuses() {
    cycle(Lane::Type, true);
}
#[test]
fn value_mdata_self_cycle_refuses() {
    cycle(Lane::Value, false);
}
#[test]
fn value_mdata_two_node_cycle_refuses() {
    cycle(Lane::Value, true);
}
#[test]
fn default_mdata_self_cycle_refuses() {
    cycle(Lane::Default, false);
}
#[test]
fn default_mdata_two_node_cycle_refuses() {
    cycle(Lane::Default, true);
}

#[test]
fn acyclic_type_spine_preserves_original_names_and_order() {
    let mut f = Fixture::new(
        Lane::Type,
        Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        None,
    );
    let outer = (f.pointer() - f.base) as usize;
    let inner = u64::from_le_bytes(f.bytes[outer + 24..outer + 32].try_into().unwrap());
    f.word(outer + 8, f.prefix);
    f.word((inner - f.base) as usize + 8, f.full_name);
    let wrapped = f.mdata(f.pointer());
    f.point_at(wrapped);
    let env = f.load().expect("acyclic type spine");
    assert_eq!(
        type_binder_names(&env, &Name::from_string(f.name)).unwrap(),
        &[Name::from_string("Root"), Name::from_string("Root.subject")]
    );
}

#[test]
fn acyclic_value_spine_preserves_lambda_count_and_forall_names() {
    let mut f = Fixture::new(
        Lane::Value,
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::type_()),
        Some(Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Implicit, Expr::prop(), Expr::prop()),
        )),
    );
    let outer = (f.pointer() - f.base) as usize;
    let inner = u64::from_le_bytes(f.bytes[outer + 24..outer + 32].try_into().unwrap());
    f.word((inner - f.base) as usize + 8, f.full_name);
    let wrapped = f.mdata(f.pointer());
    f.point_at(wrapped);
    let env = f.load().expect("acyclic value spine");
    let names = env
        .get_value_forall_binder_names(&Name::from_string(f.name))
        .unwrap();
    assert_eq!(names.lambdas, 1);
    assert_eq!(names.names, [Name::from_string("Root.subject")]);
}

#[test]
fn acyclic_default_spine_preserves_original_names_and_binder_kinds() {
    let mut f = Fixture::new(
        Lane::Default,
        Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        Some(Expr::lam(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(1)),
        )),
    );
    let outer = (f.pointer() - f.base) as usize;
    let inner = u64::from_le_bytes(f.bytes[outer + 24..outer + 32].try_into().unwrap());
    f.word(outer + 8, f.prefix);
    f.word((inner - f.base) as usize + 8, f.full_name);
    let inner_offset = (inner - f.base) as usize;
    let body = u64::from_le_bytes(
        f.bytes[inner_offset + 24..inner_offset + 32]
            .try_into()
            .unwrap(),
    );
    let imported_inner = f.lambda_with_info(inner, body, 0);
    let imported_outer = f.lambda_with_info(f.pointer(), imported_inner, 1);
    let wrapped = f.mdata(imported_outer);
    f.point_at(wrapped);
    let env = f.load().expect("acyclic default spine");
    let state = env
        .get_ext_state::<DefaultFnBinderState>(default_fn_binder_idx())
        .unwrap();
    assert_eq!(
        state.binders[&Name::from_string(f.name)],
        [
            (Name::from_string("Root.subject"), BinderInfo::Implicit),
            (
                Name::from_string("Root.subject._default"),
                BinderInfo::Default
            ),
        ]
    );
}

#[test]
fn malformed_spine_preserves_the_decode_error_instead_of_omitting_names() {
    let mut f = simple(Lane::Type);
    let pointer = f.mdata(1);
    f.bytes[(pointer - f.base) as usize + 6] = 1;
    f.point_at(pointer);
    assert!(
        matches!(f.load(), Err(ImportError::Parse(clean_olean::OleanError::Region(reason)))
        if reason.contains("malformed Expr"))
    );
}

#[test]
fn caller_deadline_remains_an_explicit_interruption() {
    let f = simple(Lane::Type);
    let mut interrupted = false;
    let done = clean_kernel::tc::run_until(Some(Instant::now()), || {
        interrupted = matches!(f.load(), Err(ImportError::Interrupted));
    });
    assert_eq!(done, None);
    assert!(interrupted);
}
