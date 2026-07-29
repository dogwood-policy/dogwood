forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && ((if false then (if false then principal else principal) else (if false then principal else principal)) in (if false then (if false then principal else principal) else (if false then principal else principal)))) && false
};
