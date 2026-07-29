permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (if (({"": {}}[""]) has "") then (context == false) else false)
};
