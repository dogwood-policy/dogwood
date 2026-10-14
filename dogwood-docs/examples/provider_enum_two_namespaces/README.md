# provider_enum_two_namespaces

The same `Vendor::ThreatScan` provider and `Vendor::Severity` enum as
`provider_enum_severity_forbid`, with an action schema that has actions in two
namespaces, `App` and `Audit`. One **unscoped** guardrail covers both:

```
@id("forbid_severe")
forbid (principal, action, resource) when {
    Vendor::ThreatScan(context.input.document).severity
        in [Vendor::Severity::"HIGH", Vendor::Severity::"CRITICAL"]
};
```

The enum is exported once, into the first namespace (`App::Vendor_Severity`), and
`Audit`'s actions refer to it by its full name. So the forbid fires on both namespaces:

- `@0`  `App::Read` `"hello"` → **ALLOW**
- `@10` `App::Read` `"malware here"` → **DENY**
- `@20` `Audit::Inspect` `"hello"` → **ALLOW**
- `@30` `Audit::Inspect` `"malware here"` → **DENY**

Referenced by `guide/05-information-providers.md`.
