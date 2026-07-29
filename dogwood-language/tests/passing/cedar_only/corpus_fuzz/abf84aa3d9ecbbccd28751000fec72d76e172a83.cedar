forbid(
  principal == a::"*",
  action == Action::"action",
  resource == a::"*"
) when {
  ((true && (a::"*".hasTag(if (a::"*".hasTag("")) then (if true then "" else "") else (if true then "" else "")))) && (("" == "") == true)) && true
};
