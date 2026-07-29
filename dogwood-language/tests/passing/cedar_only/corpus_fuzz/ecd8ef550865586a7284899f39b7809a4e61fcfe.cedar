permit(
  principal,
  action,
  resource == a::""
) when {
  (true && ((if (context has "") then 0 else 0) == 0)) && false
};
