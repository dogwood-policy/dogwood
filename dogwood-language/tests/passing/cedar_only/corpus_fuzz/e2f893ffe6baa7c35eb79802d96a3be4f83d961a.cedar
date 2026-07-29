permit(
  principal == a::"",
  action == Action::"action",
  resource is a
) when {
  true && (a::"".hasTag(if (action.hasTag("")) then (if true then "" else "") else ""))
};
