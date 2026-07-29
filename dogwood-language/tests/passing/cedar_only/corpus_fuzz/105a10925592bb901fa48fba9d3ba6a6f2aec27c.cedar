forbid(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::"\u{5}\0"
) when {
  (true && ("?" like "*?")) && ("?" like "")
};
