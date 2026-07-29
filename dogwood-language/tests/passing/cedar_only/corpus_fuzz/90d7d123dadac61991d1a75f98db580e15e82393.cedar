@YcZ100000000("")
forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && (resource in resource)) && (resource in a::"")) && true
};
