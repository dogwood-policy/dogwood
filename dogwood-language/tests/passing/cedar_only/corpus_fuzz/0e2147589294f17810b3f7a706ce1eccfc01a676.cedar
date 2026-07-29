@C("")
@MN("e/datet")
forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (resource.r)
};
