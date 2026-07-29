permit(
  principal,
  action in [M::Action::"action"],
  resource in M::a::""
) when {
  ((true && (({"": datetime("0000-01-01")} has "") && false)) && false) && false
};
