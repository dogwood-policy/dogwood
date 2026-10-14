// `GuardDuty::ThreatDetector(texts) -> { threatSeverity }`. Returns the bare
// id; with `threatSeverity` declared as an enum, Dogwood converts it to an
// entity (and denies on an id outside the enum).
fn evaluate(texts) {
    if type_of(texts) == "()" { return #{ threatSeverity: "HIGH" }; }
    let sev = "LOW";
    for t in texts {
        let t = to_lower(t);
        if t.contains("bogus") { sev = "UNKNOWN"; }
        else if t.contains("malware") { sev = "HIGH"; }
        else if t.contains("scan") && sev == "LOW" { sev = "MEDIUM"; }
    }
    #{ threatSeverity: sev }
}
