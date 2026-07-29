permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (({z: ["", "", ""]}.z).containsAny([ip("::"), ip("0.0.0.0"), ip("0.0.0.0")]))
};
