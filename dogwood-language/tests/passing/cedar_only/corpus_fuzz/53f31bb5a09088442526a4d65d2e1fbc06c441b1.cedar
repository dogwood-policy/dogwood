@Ro3R000("")
permit(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  true
};
