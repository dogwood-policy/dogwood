permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && (resource in resource)) && (resource in (if (!(((datetime("0138-04-03T00:00:00Z")).offset(duration("0ms"))) < (datetime("0000-01-01")))) then [] else []))
};
