forbid(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  ((true && ((if (!false) then (if false then (ip("::1:3536")) else (ip("0.0.0.0"))) else (ip("0.0.0.0"))).isMulticast())) && false) && false
};
