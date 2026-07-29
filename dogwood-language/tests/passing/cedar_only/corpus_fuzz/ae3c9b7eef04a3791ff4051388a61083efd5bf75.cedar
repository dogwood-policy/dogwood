permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  (true && ((if (resource in principal) then {"": false} else (if true then context else {"": false}))[""])) && false
};
