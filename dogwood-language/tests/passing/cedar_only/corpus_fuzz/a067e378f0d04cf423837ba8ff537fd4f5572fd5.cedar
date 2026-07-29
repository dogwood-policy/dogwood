forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::"                         "
) when {
  (true && ((if (principal in principal) then (if true then a::"                         " else resource) else resource) in resource)) && false
};
