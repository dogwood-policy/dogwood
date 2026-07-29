permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  (true && ((if (resource in resource) then (if false then context else context) else {"": false})[""])) && false
};
