# Pending Fix

A holding area for temporal corpus cases whose verdict stream does not match
their `expected_<n>.out`. It is currently empty.

The `harness.rs` test in this directory asserts that every case present here
still fails. If a case starts producing its expected verdict stream, the test
fails and the case should be moved to `passing/temporal_only/corpus/`.

## Layout

Cases use the same on-disk shape as the other corpora:

```
<case_name>/
  policy_1.dw           one or more policy_<n>.dw, concatenated in order
  schema.cedarschema    optional; falls back to the shared schema
  event.dwschema        optional event-schema override
  trace_<n>.log         paired with expected_<n>.out
  expected_<n>.out
```
