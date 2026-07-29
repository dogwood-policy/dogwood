forbid(
  principal == a::"\0\0\0PS",
  action,
  resource in a::""
) when {
  (true && (a::"\0\0\0PS" is a)) && ("" == (if (principal has "4") then (if false then "" else "") else ""))
};
