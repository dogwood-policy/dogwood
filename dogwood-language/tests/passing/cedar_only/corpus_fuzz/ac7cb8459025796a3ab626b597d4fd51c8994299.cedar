permit(
  principal,
  action,
  resource
) when {
  true && (if (context has "") then false else false)
};
