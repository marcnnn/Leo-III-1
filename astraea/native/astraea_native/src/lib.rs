use rustler::{Atom, Binary, Env, NifResult};
use std::collections::HashMap;

mod atoms {
    rustler::atoms! {
        gt,
        lt,
        eq,
        inc,
        err_invalid_arena,
        err_invalid_fv,
    }
}

const NODE_BYTES: usize = 12;

const TAG_CONST: u8 = 1;
const TAG_BVAR: u8 = 2;
const TAG_FVAR: u8 = 3;
const TAG_APP: u8 = 4;
const TAG_LAM: u8 = 5;
const TAG_EQ: u8 = 6;
const TAG_NOT: u8 = 7;
const TAG_OR: u8 = 8;
const TAG_FORALL: u8 = 9;
const TAG_SKOLEM: u8 = 10;
const TAG_COMB: u8 = 11;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct RawNode {
    tag: u8,
    flags: u8,
    type_id: u16,
    left: u32,
    right: u32,
}

#[inline(always)]
fn get_node(buf: &[u8], id: u32) -> Option<RawNode> {
    let offset = (id as usize).checked_mul(NODE_BYTES)?;
    let slice = buf.get(offset..offset + NODE_BYTES)?;
    Some(RawNode {
        tag: slice[0],
        flags: slice[1],
        type_id: u16::from_be_bytes([slice[2], slice[3]]),
        left: u32::from_be_bytes([slice[4], slice[5], slice[6], slice[7]]),
        right: u32::from_be_bytes([slice[8], slice[9], slice[10], slice[11]]),
    })
}

fn weight_and_vars(buf: &[u8], id: u32, vars: &mut HashMap<u32, u32>) -> Option<u32> {
    let node = get_node(buf, id)?;
    match node.tag {
        TAG_FVAR => {
            *vars.entry(node.left).or_insert(0) += 1;
            Some(1)
        }
        TAG_BVAR | TAG_CONST | TAG_COMB | TAG_SKOLEM => Some(1),
        TAG_NOT => {
            let w = weight_and_vars(buf, node.left, vars)?;
            Some(1 + w)
        }
        TAG_LAM | TAG_FORALL => {
            let w = weight_and_vars(buf, node.right, vars)?;
            Some(1 + w)
        }
        TAG_APP | TAG_EQ | TAG_OR => {
            let wl = weight_and_vars(buf, node.left, vars)?;
            let wr = weight_and_vars(buf, node.right, vars)?;
            Some(1 + wl + wr)
        }
        _ => None,
    }
}

#[inline]
fn vars_dominate(big: &HashMap<u32, u32>, small: &HashMap<u32, u32>) -> bool {
    small
        .iter()
        .all(|(k, &cnt)| big.get(k).copied().unwrap_or(0) >= cnt)
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum KboOrd {
    Gt,
    Lt,
    Eq,
    Inc,
}

fn kbo_cmp(buf: &[u8], s_id: u32, t_id: u32) -> Option<KboOrd> {
    if s_id == t_id {
        return Some(KboOrd::Eq);
    }
    let mut vs = HashMap::new();
    let mut vt = HashMap::new();
    let ws = weight_and_vars(buf, s_id, &mut vs)?;
    let wt = weight_and_vars(buf, t_id, &mut vt)?;

    let s_ge_t = vars_dominate(&vs, &vt);
    let t_ge_s = vars_dominate(&vt, &vs);

    if s_ge_t && ws > wt {
        Some(KboOrd::Gt)
    } else if t_ge_s && wt > ws {
        Some(KboOrd::Lt)
    } else if s_ge_t && t_ge_s && ws == wt {
        kbo_lex(buf, s_id, t_id)
    } else {
        Some(KboOrd::Inc)
    }
}

fn kbo_lex(buf: &[u8], s_id: u32, t_id: u32) -> Option<KboOrd> {
    let ns = get_node(buf, s_id)?;
    let nt = get_node(buf, t_id)?;

    if ns.tag != nt.tag {
        return Some(if ns.tag > nt.tag {
            KboOrd::Gt
        } else {
            KboOrd::Lt
        });
    }

    match ns.tag {
        TAG_CONST | TAG_COMB | TAG_SKOLEM | TAG_BVAR => Some(if ns.left > nt.left {
            KboOrd::Gt
        } else if ns.left < nt.left {
            KboOrd::Lt
        } else {
            KboOrd::Eq
        }),
        TAG_NOT => kbo_cmp(buf, ns.left, nt.left),
        TAG_LAM | TAG_FORALL => {
            if ns.left != nt.left {
                Some(if ns.left > nt.left {
                    KboOrd::Gt
                } else {
                    KboOrd::Lt
                })
            } else {
                kbo_cmp(buf, ns.right, nt.right)
            }
        }
        TAG_APP | TAG_EQ | TAG_OR => match kbo_cmp(buf, ns.left, nt.left)? {
            KboOrd::Eq => kbo_cmp(buf, ns.right, nt.right),
            other => Some(other),
        },
        _ => Some(KboOrd::Inc),
    }
}

fn walk_fv(buf: &[u8], term_id: u32, fv: &mut [u32; 16]) -> Option<u32> {
    let node = get_node(buf, term_id)?;
    fv[0] += 1;
    if (1..=11).contains(&node.tag) {
        fv[(node.tag as usize) + 1] += 1;
    }

    match node.tag {
        TAG_CONST => {
            let bucket = 13 + ((node.left as usize) % 3);
            fv[bucket] += 1;
            Some(1)
        }
        TAG_BVAR | TAG_FVAR | TAG_COMB | TAG_SKOLEM => Some(1),
        TAG_NOT => Some(1 + walk_fv(buf, node.left, fv)?),
        TAG_LAM | TAG_FORALL => Some(1 + walk_fv(buf, node.right, fv)?),
        TAG_APP | TAG_EQ | TAG_OR => {
            let dl = walk_fv(buf, node.left, fv)?;
            let dr = walk_fv(buf, node.right, fv)?;
            Some(1 + dl.max(dr))
        }
        _ => None,
    }
}

/// Zero-copy native Knuth-Bendix Ordering comparator over a flat 12-byte Arena binary.
#[rustler::nif]
fn nif_kbo_compare(env: Env, arena_bin: Binary, s_id: u32, t_id: u32) -> NifResult<Atom> {
    match kbo_cmp(arena_bin.as_slice(), s_id, t_id) {
        Some(KboOrd::Gt) => Ok(atoms::gt()),
        Some(KboOrd::Lt) => Ok(atoms::lt()),
        Some(KboOrd::Eq) => Ok(atoms::eq()),
        Some(KboOrd::Inc) => Ok(atoms::inc()),
        None => Err(rustler::Error::Term(Box::new(
            atoms::err_invalid_arena().to_term(env),
        ))),
    }
}

/// Zero-copy native 16-lane Feature Vector (`FVIndex`) extractor.
#[rustler::nif]
fn nif_feature_vector(env: Env, arena_bin: Binary, term_id: u32) -> NifResult<Vec<u32>> {
    let mut fv = [0u32; 16];
    match walk_fv(arena_bin.as_slice(), term_id, &mut fv) {
        Some(depth) => {
            fv[1] = depth;
            Ok(fv.to_vec())
        }
        None => Err(rustler::Error::Term(Box::new(
            atoms::err_invalid_arena().to_term(env),
        ))),
    }
}

/// SIMD-auto-vectorized 16-lane u32 Feature-Vector batch subsumption filter.
/// Checks `cand_fv[0..16] <= target_fv[0..16]` across a contiguous buffer of target FVs
/// (`64 bytes = 16 * u32-big` per target) and returns the matching target indices.
#[rustler::nif]
fn nif_fv_subsumes_batch(env: Env, cand_fv: Vec<u32>, targets_bin: Binary) -> NifResult<Vec<u32>> {
    if cand_fv.len() != 16 || targets_bin.len() % 64 != 0 {
        return Err(rustler::Error::Term(Box::new(
            atoms::err_invalid_fv().to_term(env),
        )));
    }

    let mut cand = [0u32; 16];
    cand.copy_from_slice(&cand_fv);

    let bytes = targets_bin.as_slice();
    let num_targets = bytes.len() / 64;
    let mut matches = Vec::new();

    for idx in 0..num_targets {
        let base = idx * 64;
        let mut target = [0u32; 16];
        for lane in 0..16 {
            let off = base + lane * 4;
            target[lane] = u32::from_be_bytes([
                bytes[off],
                bytes[off + 1],
                bytes[off + 2],
                bytes[off + 3],
            ]);
        }

        // Fixed 16-lane comparison loop (auto-vectorized to 4x 128-bit NEON / 2x AVX2 instructions)
        let mut subsumes = true;
        for lane in 0..16 {
            subsumes &= cand[lane] <= target[lane];
        }
        if subsumes {
            matches.push(idx as u32);
        }
    }

    Ok(matches)
}

rustler::init!("Elixir.Astraea.Native");
