permit(
  principal is TJw,
  action == Action::"action",
  resource is TJw
) when {
  ((true && ((true && ((ip("1af:af41:79af:af0f:1ff:690f:1ff:ffff/126")).isMulticast())) && false)) && false) && false
};
