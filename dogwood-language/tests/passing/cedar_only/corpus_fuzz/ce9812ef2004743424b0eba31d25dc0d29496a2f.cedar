permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in action) then (context has "") else false) then false else false)
};
