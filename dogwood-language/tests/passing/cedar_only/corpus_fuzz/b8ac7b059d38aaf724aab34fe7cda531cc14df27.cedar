@F("")
permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  true && ("\0\0" like "")
};
