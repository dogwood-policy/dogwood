forbid(
  principal == a::"",
  action in [Action::""],
  resource in a::""
) when {
  (true && ("" like "")) && ("" like "")
};
