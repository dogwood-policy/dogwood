@A000000000000000("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  ((true && (principal is a)) && (principal is a)) && (resource is a)
};
