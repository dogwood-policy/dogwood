permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((if (context has "") then [] else []).isEmpty())) && false
};
