forbid(
  principal in a::"",
  action == Action::"bian ",
  resource is a in a::""
) when {
  ((true && ([ip(""), ip(""), ip("")].containsAll([ip(""), ip(""), ip("")]))) && ([ip("::3:2b2b:152b:2b2b"), ip("0.0.0.0"), ip("0.0.0.0")].containsAll([]))) && false
};
