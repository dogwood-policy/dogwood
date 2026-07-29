forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else (if (if true then true else true) then (if true then true else true) else (if true then true else true)))) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else (if (if true then true else true) then (if true then true else true) else (if true then true else true)))) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else (if (if true then true else true) then (resource in resource) else ([].containsAny([]))))
};
