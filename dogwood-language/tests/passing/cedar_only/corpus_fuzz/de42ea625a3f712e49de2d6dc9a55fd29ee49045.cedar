forbid(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  ((true && (if (if (if false then false else false) then false else false) then false else true)) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else false)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else (if (if true then true else true) then (if true then true else true) else (if true then true else true)))) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if false then false else false) then false else ([].containsAny([duration("0s")]))) else false)
};
