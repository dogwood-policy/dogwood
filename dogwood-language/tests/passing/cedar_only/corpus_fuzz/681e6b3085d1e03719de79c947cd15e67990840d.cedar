forbid(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && ((if (action in a::"") then a::"" else a::"") in a::"")) && false) && false
};
