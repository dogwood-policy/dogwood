forbid(
  principal in a::"\0\0",
  action == Action::"action",
  resource
) when {
  ((true && ((a::"\0\0" is a) && ((if false then {"": true} else {"": false})[""]))) && false) && false
};
