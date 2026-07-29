forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ([{"": false}, {"": true}].contains(if (principal in action) then {"": false} else {"": true}))) && false) && false
};
