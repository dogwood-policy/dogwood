forbid(
  principal == a::"\0\0\0PS",
  action,
  resource in a::"\0\0\0PS"
) when {
  (true && (a::"\0\0\0PS" is a)) && ("" == (if (principal has "") then (if false then "4" else "") else ":"))
};
