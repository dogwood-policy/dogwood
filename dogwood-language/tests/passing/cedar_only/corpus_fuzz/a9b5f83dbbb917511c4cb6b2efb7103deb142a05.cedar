@I("")
permit(
  principal == r::"",
  action,
  resource in r::""
) when {
  true && ((ip("")).isMulticast())
};
