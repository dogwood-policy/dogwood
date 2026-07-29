permit(
  principal,
  action,
  resource
) when {
  (true && ((if (principal has "") then (if false then "" else "") else "44444444") == (if (principal has "3") then "" else ""))) && (!(!(principal has "4444444")))
};
