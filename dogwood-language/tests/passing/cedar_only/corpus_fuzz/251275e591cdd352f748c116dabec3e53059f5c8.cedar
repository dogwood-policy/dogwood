@bo0("")
forbid(
  principal == a::"\0",
  action == Action::"action",
  resource == a::"\0"
) when {
  ((true && (if (a::"\0".hasTag(if true then "" else "")) then (a::"\0".hasTag(if true then "" else "")) else (a::"\0".hasTag("")))) && false) && true
};
