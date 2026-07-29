forbid(
  principal in g3::"\u{4}\u{4}",
  action in [Action::"action"],
  resource is Pf in l::"\0\0\0\0\0\0\0\0\0\0\0Debian \0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0@\n\0\0\0\0"
) when {
  (true && ((resource.getTag("")).greaterThan(resource.getTag("")))) && ("" like "")
};
