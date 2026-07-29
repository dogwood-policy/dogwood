@A("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((if (resource in a::"") then (if false then a::"" else principal) else principal) in principal)
};
