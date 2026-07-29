permit(
  principal,
  action,
  resource is M::a in M::a::""
) when {
  true && (action in M::a::"\u{19}")
};
