permit(
  principal is a,
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (({"IIIIII\0\0": ip("0.0.0.0")}["IIIIII\0\0"]) == (if ((ip("::91:4949:4949:4949:4949:4949")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))))
};
