forbid(
  principal is a in a::"\0\0",
  action,
  resource
) when {
  (true && ((if false then ["", "", ""] else [""]) == ["", ""])) && false
};
