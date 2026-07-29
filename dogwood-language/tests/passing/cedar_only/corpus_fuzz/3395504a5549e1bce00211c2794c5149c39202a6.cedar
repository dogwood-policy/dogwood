permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  ((true && ((ip("")) == (ip("")))) && ((if ((ip("0.1.32.4")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))) == (ip("0.0.0.0")))) && false
};
