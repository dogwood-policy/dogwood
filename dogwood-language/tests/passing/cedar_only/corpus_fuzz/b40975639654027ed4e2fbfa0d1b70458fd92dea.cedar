forbid(
  principal == a::"",
  action in [Action::"ipadd"],
  resource == a::""
) when {
  true
};
