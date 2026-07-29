forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ({"": {}} == {"": {"": decimal("0.27")}})) && false
};
