forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && ((if (a::"" == a::"") then (if true then [a::"", a::"", a::""] else [a::"", a::"", a::""]) else (if true then [a::"", a::"", a::""] else [a::"", a::"", a::""])).containsAny([a::"", a::"", principal]))
};
