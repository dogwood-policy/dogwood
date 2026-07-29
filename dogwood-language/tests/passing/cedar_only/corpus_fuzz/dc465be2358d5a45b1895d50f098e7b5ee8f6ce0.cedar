forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  ((true && ([context, context].contains(if (action in principal) then {"": true, "00:": {}} else {"": true, "00:": {}}))) && false) && false
};
