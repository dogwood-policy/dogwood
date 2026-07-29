forbid(
  principal == a::"",
  action,
  resource in a::""
) when {
  (true && (false || (false || ([].contains(false))))) && false
};
