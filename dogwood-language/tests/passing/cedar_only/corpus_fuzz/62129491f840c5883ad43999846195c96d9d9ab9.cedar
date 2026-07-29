permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in action) then ({"": decimal("3.3282")} has "") else false) then false else false)
};
