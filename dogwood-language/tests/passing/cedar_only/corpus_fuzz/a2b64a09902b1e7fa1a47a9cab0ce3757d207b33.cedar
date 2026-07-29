permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in action) then ({"": ip("0.0.0.0"), "}": decimal("0.0")} has "") else false) then false else false)
};
