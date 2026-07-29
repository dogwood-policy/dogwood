permit(
  principal,
  action in [],
  resource
) when {
  true && ((if (context has "") then false else false) || false)
};
