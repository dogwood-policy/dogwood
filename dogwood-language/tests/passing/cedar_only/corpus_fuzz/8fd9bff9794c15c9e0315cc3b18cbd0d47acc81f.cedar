forbid(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  ((true && (if (if (if false then false else false) then false else false) then false else true)) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else false)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else (if (if true then true else true) then (if true then true else false) else (action in action)))) && (if (if (if true then true else true) then (if true then true else true) else (if true then true else false)) then (({"": action}[""]) in (context[""])) else (a::"" in resource))
};
