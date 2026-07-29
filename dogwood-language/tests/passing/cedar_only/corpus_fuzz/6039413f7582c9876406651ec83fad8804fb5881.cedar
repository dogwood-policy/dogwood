@XDM17PPPP("")
permit(
  principal == a::":1",
  action in [Action::"action"],
  resource == a::""
) when {
  true && (a::":1" has "")
};
