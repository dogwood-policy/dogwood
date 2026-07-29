@A0000("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((({g: {"[": action}}.g)["["]) in action)) && true
};
