forbid(
  principal in a::"\0Debian \0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0Debian \0\0"
) when {
  (true && (resource is a)) && ("?Debian a\0\0\0\0" like "\0\0*")
};
