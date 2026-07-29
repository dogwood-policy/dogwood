permit(
  principal == a::"",
  action in [],
  resource in a::""
) when {
  ((true && ((if (principal in principal) then (if false then principal else principal) else (if false then principal else principal)) in (if (principal in principal) then (if false then principal else principal) else (if true then principal else principal)))) && ((if (principal in principal) then (if false then principal else principal) else (if false then principal else principal)) in (if (principal in principal) then (if true then principal else principal) else (if false then principal else principal)))) && ((if (principal in principal) then (if false then principal else principal) else (if false then principal else principal)) in (if (principal in principal) then a::"" else a::""))
};
