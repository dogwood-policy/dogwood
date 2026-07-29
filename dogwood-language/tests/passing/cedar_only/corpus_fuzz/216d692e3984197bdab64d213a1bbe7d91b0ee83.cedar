permit(
  principal == a::"\0",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && (if (if (if false then false else false) then (principal in resource) else ([ip("21aa:7272:f3c:1ff:f780:1212:120a:0/0")].containsAll([datetime("5394-07-28")]))) then false else false)) && true
};
