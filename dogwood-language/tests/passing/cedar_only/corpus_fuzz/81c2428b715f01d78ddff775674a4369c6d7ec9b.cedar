permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((false && (a::"" in principal)) && false)) && (false && (if (if true then true else true) then true else false))
};
