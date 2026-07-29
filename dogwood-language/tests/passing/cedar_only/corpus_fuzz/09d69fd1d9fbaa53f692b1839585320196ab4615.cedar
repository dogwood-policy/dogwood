forbid(
  principal,
  action,
  resource
) when {
  (true && ((if ("" like "R\u{17}\0\0\0\0") then context else context)[""])) && false
};
