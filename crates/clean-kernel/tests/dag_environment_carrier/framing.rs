// Copyright 2026 Andrew Yates | Apache-2.0
//! Independently authored hostile V2 framing, not a production codec oracle.
#[derive(Clone)]
pub(super) struct Envelope {
    pub(super) magic: [u8; 8],
    pub(super) environment: Vec<u8>,
    pub(super) nodes: Vec<Node>,
}
#[derive(Clone)]
pub(super) struct Node {
    pub(super) id: u32,
    pub(super) kind: Vec<u8>,
}
fn bytes(out: &mut Vec<u8>, value: &[u8]) {
    out.extend_from_slice(&(value.len() as u64).to_le_bytes());
    out.extend_from_slice(value);
}
pub(super) fn encode(wire: &Envelope) -> Vec<u8> {
    let mut out = wire.magic.to_vec();
    out.extend_from_slice(&2u32.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    bytes(&mut out, &wire.environment);
    out.extend_from_slice(&(wire.nodes.len() as u64).to_le_bytes());
    for node in &wire.nodes {
        out.extend_from_slice(&node.id.to_le_bytes());
        bytes(&mut out, &node.kind);
    }
    out
}
fn take<'a>(input: &mut &'a [u8], size: usize) -> &'a [u8] {
    let (value, rest) = input.split_at(size);
    *input = rest;
    value
}
fn u64_value(input: &mut &[u8]) -> usize {
    usize::try_from(u64::from_le_bytes(take(input, 8).try_into().unwrap())).unwrap()
}
fn payload(input: &mut &[u8]) -> Vec<u8> {
    let n = u64_value(input);
    take(input, n).to_vec()
}
pub(super) fn envelope(mut input: &[u8]) -> Envelope {
    let magic = take(&mut input, 8).try_into().unwrap();
    assert_eq!(take(&mut input, 4), 2u32.to_le_bytes());
    assert_eq!(take(&mut input, 4), 0u32.to_le_bytes());
    let environment = payload(&mut input);
    let count = u64_value(&mut input);
    let mut nodes = Vec::new();
    for _ in 0..count {
        let id = u32::from_le_bytes(take(&mut input, 4).try_into().unwrap());
        nodes.push(Node {
            id,
            kind: payload(&mut input),
        });
    }
    assert!(input.is_empty());
    Envelope {
        magic,
        environment,
        nodes,
    }
}
pub(super) fn app(left: u32, right: u32) -> Vec<u8> {
    [4u32.to_le_bytes(), left.to_le_bytes(), right.to_le_bytes()].concat()
}
pub(super) fn bvar(index: u32) -> Vec<u8> {
    [0u32.to_le_bytes(), index.to_le_bytes()].concat()
}
pub(super) fn sort_zero() -> Vec<u8> {
    [2u32.to_le_bytes(), 0u32.to_le_bytes()].concat()
}
pub(super) fn deep_name_const(depth: usize) -> Vec<u8> {
    let mut name = 0u32.to_le_bytes().to_vec();
    for _ in 0..depth {
        let mut outer = 1u32.to_le_bytes().to_vec();
        outer.extend(name);
        bytes(&mut outer, b"n");
        name = outer;
    }
    let mut kind = 3u32.to_le_bytes().to_vec();
    kind.extend(name);
    kind.extend_from_slice(&0u64.to_le_bytes());
    kind
}
