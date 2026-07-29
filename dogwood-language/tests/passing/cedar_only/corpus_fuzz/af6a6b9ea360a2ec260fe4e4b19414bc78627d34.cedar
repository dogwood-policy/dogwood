@A0000000000000("")
permit(
  principal == a::"*",
  action == Action::"action",
  resource == a::"*"
) when {
  ((true && (a::"*".hasTag(if (a::"*".hasTag("")) then "" else ""))) && true) && true
};
