forbid(
  principal in a::"",
  action,
  resource
) when {
  ((true && ((if ({"": false}[""]) then {"": false} else context)[""])) && false) && false
};
