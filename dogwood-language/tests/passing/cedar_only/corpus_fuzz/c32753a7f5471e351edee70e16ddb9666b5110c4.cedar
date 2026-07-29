permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (if (resource in resource) then (context[""]) else (principal in principal)) then (resource in principal) else (resource in resource))
};
