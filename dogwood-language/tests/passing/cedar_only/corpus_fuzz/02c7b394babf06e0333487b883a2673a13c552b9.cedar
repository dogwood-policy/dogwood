forbid(
  principal,
  action,
  resource
) when {
  (true && (if ("GGG" like "******") then true else true)) && false
};
