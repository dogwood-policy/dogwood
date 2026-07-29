forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ((if (["ia", "n"] == []) then {"": true} else context)[""])) && false
};
