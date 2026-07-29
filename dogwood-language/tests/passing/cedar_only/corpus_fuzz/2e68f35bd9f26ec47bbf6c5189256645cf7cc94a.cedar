forbid(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (!(((datetime("2125-06-02T02:00:00Z")).offset(duration("0ms"))) < (datetime("0000-01-01"))))) && false
};
