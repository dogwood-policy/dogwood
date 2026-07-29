permit(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && (((resource.getTag("bbb")).getTag("")) in resource)) && false
};
