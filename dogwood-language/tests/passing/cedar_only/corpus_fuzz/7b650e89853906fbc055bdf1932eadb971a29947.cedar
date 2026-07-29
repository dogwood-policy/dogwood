forbid(
  principal in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ("4.." like "*..")) && false
};
