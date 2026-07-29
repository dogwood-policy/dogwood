permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  true && ((ip("::5f5f:5f49:4925")) == (ip("0.0.0.0")))
};
