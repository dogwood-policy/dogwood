@_0000000000000("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ({} has "") then context else {"": true})[""])
};
