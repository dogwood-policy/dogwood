permit(
  principal is a,
  action,
  resource is a
) when {
  true && ((if (principal in resource) then principal else a::"") in principal)
};
