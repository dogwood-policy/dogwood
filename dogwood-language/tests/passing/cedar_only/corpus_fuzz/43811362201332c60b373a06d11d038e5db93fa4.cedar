forbid(
  principal in r::"",
  action in [Action::"action"],
  resource
) when {
  (true && ([{}, {}, {}].contains(context))) && (if false then false else false)
};
