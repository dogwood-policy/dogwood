forbid(
  principal == a::"@",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0")).isInRange(ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")))) || (if (if false then false else false) then (if false then false else false) else (if false then true else false)))
};
