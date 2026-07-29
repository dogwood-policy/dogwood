permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in action) then ({} has "") else (action in a::"")) then ({"": false}[""]) else false)
};
