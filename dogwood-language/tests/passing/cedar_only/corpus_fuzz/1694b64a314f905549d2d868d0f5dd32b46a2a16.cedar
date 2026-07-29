forbid(
  principal in saYA000VVVVVV::"\u{e}",
  action in [Action::"action"],
  resource in saYA000VVVVVV::"\u{e}"
) when {
  (true && (false || (g3::"\0" in [action, principal]))) && false
};
