permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  (true && ((if false then {"": false} else {"": false})[""])) && (resource in resource)
};
