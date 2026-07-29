permit(
  principal is a,
  action == Action::":;",
  resource is a
) when {
  ((true && ([ip(""), ip(""), ip("")].containsAll([ip(""), ip(""), ip("")]))) && ([ip(""), ip(""), ip("")].containsAll([ip(""), ip(""), ip("")]))) && ([ip(""), ip(""), ip("")].containsAll([ip(""), ip(""), {"": ip("::2b2b:2b2b:2b2b:2b2b")}[""]]))
};
