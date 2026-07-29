forbid(
  principal is a,
  action,
  resource is a in a::""
) when {
  ((true && (((principal in principal) || false) || true)) && ((resource in a::"") || ((if false then true else false) || true))) && false
};
