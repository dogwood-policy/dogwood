@W("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if true then true else true) else (if true then true else true)) else true)
};
