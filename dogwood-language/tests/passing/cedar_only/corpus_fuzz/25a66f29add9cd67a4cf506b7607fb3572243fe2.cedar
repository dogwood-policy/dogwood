permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((if ({"": true}[""]) then a::"" else a::"") has "")) && true
};
