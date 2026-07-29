forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && (resource is a)) && ("?Da\0\0\0\0۹?\0\0\0۹?De" like "*۹?**\0\0\0۹")
};
