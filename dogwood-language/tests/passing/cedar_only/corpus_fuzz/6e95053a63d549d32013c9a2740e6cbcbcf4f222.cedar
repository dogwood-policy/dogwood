forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && (if (if (if true then true else true) then ([].contains(resource)) else (principal in resource)) then ({"": false}[""]) else false)) && false) && false
};
