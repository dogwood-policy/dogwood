@A("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && ([[]].contains([false, true, false]))
};
