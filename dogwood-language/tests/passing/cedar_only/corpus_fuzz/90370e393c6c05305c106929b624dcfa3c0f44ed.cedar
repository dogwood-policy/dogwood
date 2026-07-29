@w380("")
forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && ({} == {})) && (principal in [])
};
