@q("")
forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ((if false then "?a" else "?a") like "?a")) && false
};
