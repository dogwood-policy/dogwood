forbid(
  principal in a::"\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0"
) when {
  (true && ("" like "*\0*\0")) && ("=Debian a\0\0\0\0" like "")
};
