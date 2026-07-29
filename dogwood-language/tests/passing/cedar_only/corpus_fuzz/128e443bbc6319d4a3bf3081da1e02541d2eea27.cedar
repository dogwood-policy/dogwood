forbid(
  principal == a::"",
  action == Action::"",
  resource
) when {
  true && (((context has "") || false) || false)
};
