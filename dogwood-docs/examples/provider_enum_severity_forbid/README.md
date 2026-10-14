# provider_enum_severity_forbid

A provider that returns a value from a fixed list. `Vendor::ThreatScan(text)` returns
`{ severity }`, where `severity` is the enum `Vendor::Severity` (`LOW`, `MEDIUM`, `HIGH`,
`CRITICAL`), declared under `entityTypes` in `providers.json`. A `forbid` blocks HIGH and
CRITICAL, alongside a catch-all `permit`:

```
@id("forbid_severe")
forbid (...) when {
    Vendor::ThreatScan(context.input.document).severity
        in [Vendor::Severity::"HIGH", Vendor::Severity::"CRITICAL"]
};
```

The script (`threat_scan.rhai`, inlined into `providers.json`) returns the bare id, and
Dogwood converts it to the enum value. The trace:

- `@0`  `"hello"` (LOW) → **ALLOW**
- `@10` `"port scan"` (MEDIUM) → **ALLOW**
- `@20` `"malware here"` (HIGH) → **DENY** by `forbid_severe`
- `@30` `"ransomware"` (CRITICAL) → **DENY** by `forbid_severe`
- `@40` `"garbled"`: the script returns `SEVERE`, which isn't a declared value → **DENY**
  (fail closed), with `` `SEVERE` is not a member of `Vendor::Severity` ``

Misspelling a value in the policy (`Vendor::Severity::"CRITCAL"`) fails `dogwood validate`.
With a plain string field, the same typo would validate and the forbid would never fire.

Referenced by `guide/05-information-providers.md`.
