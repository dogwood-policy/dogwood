permit(
  principal,
  action,
  resource
) when {
  (true && ((if (principal has "") then (if false then "" else "") else (if false then "4444" else "")) == "")) && (!(!(principal has "444444444")))
};
