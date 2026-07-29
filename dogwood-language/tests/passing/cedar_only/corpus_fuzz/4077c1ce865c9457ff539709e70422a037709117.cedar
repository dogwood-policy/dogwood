permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((if (resource in principal) then [{"": [(-9042594174707687135)]}, {"": [0, 0]}, context] else []) == (datetime("0000-01-01")))) && false) && false
};
