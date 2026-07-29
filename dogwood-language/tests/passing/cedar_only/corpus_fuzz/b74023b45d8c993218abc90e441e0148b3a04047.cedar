permit(
  principal,
  action,
  resource == a::""
) when {
  (true && ((if ({"": datetime("0000-01-01")} has "") then 0 else 0) == 0)) && false
};
