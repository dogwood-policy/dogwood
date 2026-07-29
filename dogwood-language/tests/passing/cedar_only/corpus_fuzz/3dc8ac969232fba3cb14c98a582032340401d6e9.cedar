@ja("A")
@z("")
forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true
};
