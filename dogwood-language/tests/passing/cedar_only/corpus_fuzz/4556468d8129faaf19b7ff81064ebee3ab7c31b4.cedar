@h44000000000("")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && (if ((resource.getTag("")) has "") then false else false)
};
