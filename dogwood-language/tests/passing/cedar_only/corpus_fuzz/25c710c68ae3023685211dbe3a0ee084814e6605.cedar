permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in action) then ({} has "") else false) then false else false)
};
