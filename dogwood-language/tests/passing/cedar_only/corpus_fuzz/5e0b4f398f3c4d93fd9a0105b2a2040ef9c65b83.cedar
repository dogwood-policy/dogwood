permit(
  principal,
  action,
  resource
) when {
  (true && ((if (principal has "") then (context[""]) else (if false then "" else "")) == (if (principal has "4\u{1}") then "\0\0\u{4}" else "4"))) && false
};
