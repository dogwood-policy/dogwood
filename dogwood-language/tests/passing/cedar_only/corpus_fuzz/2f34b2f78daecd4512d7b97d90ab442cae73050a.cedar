@E00cZ000000("")
forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ((principal in principal) == (principal in principal))) && (principal in resource)
};
