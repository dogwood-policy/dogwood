forbid(
  principal == a::"\0\0\0PS",
  action,
  resource in a::"\0\0\0PS"
) when {
  (true && (a::"\0\0\0PS" is a)) && ((if (principal is a) then "0" else "") == "3")
};
