@v("")
forbid(
  principal,
  action in [r::r::h::r::Action::"action"],
  resource == r::r::h::r::a::""
) when {
  true
};
