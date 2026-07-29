permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((if (resource in principal) then [{"": (datetime("5703-11-07")).offset(duration("0ms"))}, context] else []) == (datetime("0000-01-01")))) && false) && false
};
