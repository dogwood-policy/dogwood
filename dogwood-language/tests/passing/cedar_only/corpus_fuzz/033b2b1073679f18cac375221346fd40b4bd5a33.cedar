forbid(
  principal == a::"",
  action,
  resource
) when {
  true && (principal in principal)
};
