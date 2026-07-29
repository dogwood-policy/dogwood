permit(
  principal in a::"",
  action,
  resource
) when {
  ((true && (if ((if true then principal else resource) is a) then ((if false then principal else principal) in (if false then action else principal)) else false)) && false) && false
};
