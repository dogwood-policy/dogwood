permit(
  principal == a::"",
  action,
  resource
) when {
  true && (if (if ({} has "\0\0") then false else false) then false else true)
};
