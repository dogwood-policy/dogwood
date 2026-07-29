forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && ("" like "*m*")) && (a::"" in a::"\0\0\0\0")
};
