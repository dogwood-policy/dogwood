permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((if ((ip("::38:3838:3838:3800:0")).isLoopback()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isLoopback())
};
