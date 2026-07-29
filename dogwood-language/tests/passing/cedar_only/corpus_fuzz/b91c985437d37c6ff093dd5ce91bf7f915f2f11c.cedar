forbid(
  principal in a::"\0",
  action == Action::"action",
  resource in a::"\0"
) when {
  (true && ((if (principal in principal) then (if false then principal else principal) else (if false then principal else principal)) in (if false then (if false then principal else principal) else (if false then principal else principal)))) && ((if (principal in principal) then (if false then principal else principal) else principal) in principal)
};
