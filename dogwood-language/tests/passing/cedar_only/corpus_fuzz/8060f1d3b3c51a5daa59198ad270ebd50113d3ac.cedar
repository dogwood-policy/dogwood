permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((if (resource in principal) then [{"": []}, {"": [549336793218, 0]}] else []) == (datetime("0000-01-01")))) && false) && false
};
