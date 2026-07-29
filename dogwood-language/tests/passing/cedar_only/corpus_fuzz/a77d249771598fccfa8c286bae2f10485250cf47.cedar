permit(
  principal,
  action == Action::":;",
  resource
) when {
  (true && (resource in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0")) && (true == (ip("85.226.255.59/19")))
};
