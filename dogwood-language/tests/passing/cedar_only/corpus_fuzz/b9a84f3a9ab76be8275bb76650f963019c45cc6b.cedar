permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (((resource in resource) && (action in action)) && (!(!(((datetime("6634-07-18T10:32:00Z")).offset(duration("0ms"))) < (datetime("0000-01-01"))))))
};
