forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  ((true && (a::"".hasTag(if (a::"".hasTag("")) then (if true then "" else "") else (if true then "R\0" else "")))) && ((if ("0" == "") then "" else "") == "")) && false
};
