permit(
  principal is a in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && (({"\0\0\0\0": ip("0.0.0.0")}["\0\0\0\0"]) == (({IIIII: {II: ip("::")}}.IIIII).II))) && false
};
