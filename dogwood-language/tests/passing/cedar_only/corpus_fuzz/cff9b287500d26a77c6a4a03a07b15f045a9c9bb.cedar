@r("")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((((ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")).isMulticast()) || false) || (true || ((ip("116.116.116.116")).isMulticast())))) && (a::"" has M)
};
