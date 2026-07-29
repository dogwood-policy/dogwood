permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ((if (principal in principal) then (if true then (ip("ff¢0:6e61:6960:6544:ffff:ffff:ffff:ffff/126")) else (ip("0.0.0.0"))) else (ip("0.0.0.0"))).isMulticast())) && false) && false
};
