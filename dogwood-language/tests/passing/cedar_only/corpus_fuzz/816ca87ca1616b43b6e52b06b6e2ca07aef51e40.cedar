forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0\0"
) when {
  (true && (resource is a)) && ("?Debi" like "?D*e")
};
