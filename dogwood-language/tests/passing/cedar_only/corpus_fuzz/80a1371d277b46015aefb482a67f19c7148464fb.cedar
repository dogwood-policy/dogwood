forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"" in [principal])) && false
};
