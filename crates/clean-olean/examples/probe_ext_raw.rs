// Audit probe (lane B, 2026-07-09): walk ModuleData.entries at the RAW object
// level, bypassing the (Name x DataValue) pair heuristic in
// module/extensions.rs, to measure what real Lean 4.30 oleans actually store
// per extension — including entries the heuristic silently drops — across all
// three olean parts (exported / server / private).
//
// Usage:
//   cargo run -p clean-olean --example probe_ext_raw -- <file.olean> [ext-substr] [N]
use clean_olean::{is_ptr, unbox_scalar, CompactedRegion, OleanHeader};

fn header_size(bytes: &[u8]) -> usize {
    match bytes.get(5) {
        Some(&2) => clean_olean::header::HEADER_SIZE_V2,
        _ => clean_olean::HEADER_SIZE,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = std::path::PathBuf::from(args.get(1).cloned().unwrap_or_default());
    let filter = args.get(2).cloned().unwrap_or_default();
    let n: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(6);

    let base_bytes = std::fs::read(&path).expect("read base olean");
    let base_header = OleanHeader::parse(&base_bytes).expect("parse base header");

    // Part 1: exported.
    {
        let region = CompactedRegion::new(&base_bytes, base_header.base_addr);
        let root = region
            .read_u64_at(header_size(&base_bytes))
            .expect("root ptr");
        println!("#### part: exported");
        dump_entries(&region, root, &filter, n);
    }

    // Parts 2/3: server & private via the combined-region recipe used by
    // parse_module_incremental (base < server < private address layout).
    let server_bytes = std::fs::read(path.with_extension("olean.server")).ok();
    let private_bytes = std::fs::read(path.with_extension("olean.private")).ok();

    for (label, part_bytes, with_server) in [
        ("server", server_bytes.clone(), false),
        ("private", private_bytes, true),
    ] {
        let Some(pb) = part_bytes else { continue };
        let part_header = OleanHeader::parse(&pb).expect("parse part header");
        let base_end = base_header.base_addr + base_bytes.len() as u64;
        let gap = (part_header.base_addr - base_end) as usize;
        let mut combined = Vec::with_capacity(base_bytes.len() + gap + pb.len());
        combined.extend_from_slice(&base_bytes);
        combined.resize(base_bytes.len() + gap, 0);
        if with_server {
            if let Some(sb) = server_bytes.as_deref() {
                if let Ok(sh) = OleanHeader::parse(sb) {
                    let off = (sh.base_addr - base_header.base_addr) as usize;
                    if off + sb.len() <= combined.len() {
                        combined[off..off + sb.len()].copy_from_slice(sb);
                    }
                }
            }
        }
        let part_start = combined.len();
        combined.extend_from_slice(&pb);
        let region = CompactedRegion::new(&combined, base_header.base_addr);
        let root = region
            .read_u64_at(part_start + header_size(&pb))
            .expect("part root ptr");
        println!("\n#### part: {label}");
        dump_entries(&region, root, &filter, n);
    }
}

/// ModuleData ptr-field order: imports(0) constNames(1) constants(2)
/// extraConstNames(3) entries(4). Fields start at offset+8.
fn dump_entries(region: &CompactedRegion, root: u64, filter: &str, n: usize) {
    let offset = region.ptr_to_offset(root).expect("root offset");
    let entries_ptr = region.read_u64_at(offset + 8 + 32).expect("entries ptr");
    if !is_ptr(entries_ptr) {
        println!("  <no entries array>");
        return;
    }
    let arr_off = region.ptr_to_offset(entries_ptr).expect("entries offset");
    let size = region.read_u64_at(arr_off + 8).expect("entries size") as usize;
    println!("  extensions: {size}");
    for i in 0..size {
        let pair_ptr = region.read_u64_at(arr_off + 24 + i * 8).expect("pair ptr");
        let pair_off = region.ptr_to_offset(pair_ptr).expect("pair offset");
        let name_ptr = region.read_u64_at(pair_off + 8).expect("ext name ptr");
        let name_off = region.ptr_to_offset(name_ptr).expect("name offset");
        let ext_name = region
            .read_name_at(name_off)
            .unwrap_or_else(|_| "<bad name>".into());
        let inner_ptr = region.read_u64_at(pair_off + 16).expect("inner ptr");
        let (raw_len, ptr_elems, scalar_elems) = if is_ptr(inner_ptr) {
            let inner_off = region.ptr_to_offset(inner_ptr).expect("inner offset");
            let len = region.read_u64_at(inner_off + 8).expect("inner size") as usize;
            let mut ptrs = 0usize;
            let mut scalars = 0usize;
            for j in 0..len {
                let e = region
                    .read_u64_at(inner_off + 24 + j * 8)
                    .expect("inner elem");
                if is_ptr(e) {
                    ptrs += 1;
                } else {
                    scalars += 1;
                }
            }
            (len, ptrs, scalars)
        } else {
            (0, 0, 0)
        };
        println!("  {ext_name:60} raw_len={raw_len:<6} ptr_elems={ptr_elems:<6} scalar_elems={scalar_elems}");
        if !filter.is_empty() && ext_name.contains(filter) && is_ptr(inner_ptr) {
            let inner_off = region.ptr_to_offset(inner_ptr).expect("inner offset");
            for j in 0..raw_len.min(n) {
                let e = region
                    .read_u64_at(inner_off + 24 + j * 8)
                    .expect("inner elem");
                if !is_ptr(e) {
                    println!("    [{j}] scalar {:#x} (unboxed {})", e, unbox_scalar(e));
                    continue;
                }
                describe_object(region, e, j, 1);
            }
        }
    }
}

/// Print an object's header (tag / #ptr-fields / size) and shallow field info.
fn describe_object(region: &CompactedRegion, ptr: u64, idx: usize, depth: usize) {
    let pad = "    ".repeat(depth);
    let Ok(off) = region.ptr_to_offset(ptr) else {
        println!("{pad}[{idx}] <ptr out of region {ptr:#x}>");
        return;
    };
    let Ok(h) = region.read_header_at(off) else {
        println!("{pad}[{idx}] <bad header>");
        return;
    };
    // Try to render as a Name first (many entries are Names or start with one).
    let as_name = region.read_name_at(off).ok();
    println!(
        "{pad}[{idx}] tag={} other(num_fields)={} cs_sz={}{}",
        h.tag,
        h.other,
        h.cs_sz,
        as_name
            .map(|s| format!("  as_name={s}"))
            .unwrap_or_default()
    );
    if h.is_constructor() && depth < 3 {
        for f in 0..(h.other as usize).min(6) {
            let Ok(fptr) = region.read_u64_at(off + 8 + f * 8) else {
                continue;
            };
            if is_ptr(fptr) {
                describe_object(region, fptr, f, depth + 1);
            } else {
                println!(
                    "{pad}    [{f}] scalar {:#x} (unboxed {})",
                    fptr,
                    unbox_scalar(fptr)
                );
            }
        }
    }
}
