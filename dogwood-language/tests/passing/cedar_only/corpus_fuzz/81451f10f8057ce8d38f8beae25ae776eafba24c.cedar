@r("")
permit(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ("?a" like "*?a")) && false
};
