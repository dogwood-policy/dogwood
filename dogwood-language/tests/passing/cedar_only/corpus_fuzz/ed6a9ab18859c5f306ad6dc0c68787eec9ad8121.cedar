@r("")
permit(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (principal in a::"")) && ((if (resource in resource) then a::"" else a::"") in [resource, a::""])
};
