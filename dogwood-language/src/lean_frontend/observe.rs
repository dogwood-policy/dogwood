//! The observables of a lowered set, and their comparison. The observables are
//! every component the crate's `Lowered` and `SetIdentity` hold, in the Lean
//! frontend's result format (the export's `lowered_record`). The shadow mode
//! compares two lowered sets by comparing their observables, and the decoder's
//! tests check that decoding inverts this encoding.

use serde_json::{Value as Json, json};

use crate::api::Lowered;
use crate::identity::SetIdentity;

/// The observables of `lowered` with its identity.
pub(crate) fn lowered(lowered: &Lowered, identity: &SetIdentity) -> Json {
    crate::api::frontend_export::lowered_record(lowered, identity)
}

/// The first place where `a` and `b` differ, as a path into them and the two
/// values there; `None` when they are equal.
pub(crate) fn first_difference(a: &Json, b: &Json) -> Option<(String, Json, Json)> {
    fn go(path: &mut String, a: &Json, b: &Json) -> Option<(String, Json, Json)> {
        match (a, b) {
            (Json::Object(x), Json::Object(y)) => {
                let mut keys: Vec<&String> = x.keys().chain(y.keys()).collect();
                keys.sort();
                keys.dedup();
                for k in keys {
                    let (u, v) = (
                        x.get(k).unwrap_or(&Json::Null),
                        y.get(k).unwrap_or(&Json::Null),
                    );
                    let len = path.len();
                    path.push('.');
                    path.push_str(k);
                    if let Some(d) = go(path, u, v) {
                        return Some(d);
                    }
                    path.truncate(len);
                }
                None
            }
            (Json::Array(x), Json::Array(y)) => {
                for (i, (u, v)) in x.iter().zip(y).enumerate() {
                    let len = path.len();
                    path.push_str(&format!("[{i}]"));
                    if let Some(d) = go(path, u, v) {
                        return Some(d);
                    }
                    path.truncate(len);
                }
                if x.len() != y.len() {
                    return Some((format!("{path} (length)"), json!(x.len()), json!(y.len())));
                }
                None
            }
            _ if a == b => None,
            _ => Some((path.clone(), a.clone(), b.clone())),
        }
    }
    go(&mut String::new(), a, b)
}
