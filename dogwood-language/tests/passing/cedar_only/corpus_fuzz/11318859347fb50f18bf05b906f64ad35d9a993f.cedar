forbid(
  principal in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((duration("0ms")) == context)) && false
};
