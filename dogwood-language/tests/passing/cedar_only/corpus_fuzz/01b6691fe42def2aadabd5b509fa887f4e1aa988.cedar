permit(
  principal,
  action,
  resource == a::""
) when {
  true && (if ({"": false, "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\02\0\0\0\0\0\0": true, "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{4}\0\0\0\0\0\0\0\0\0\0": true} has "ah\0") then false else false)
};
