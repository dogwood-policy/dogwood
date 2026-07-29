permit(
  principal,
  action,
  resource
) when {
  true && ((ip("68.42.0.0")).isMulticast())
};
