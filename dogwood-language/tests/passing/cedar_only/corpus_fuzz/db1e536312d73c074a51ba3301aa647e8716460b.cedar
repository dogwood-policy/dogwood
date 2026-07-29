permit(
  principal,
  action,
  resource
) when {
  (true && ([datetime("0000-07-07T00:00:00Z"), datetime("0000-01-01"), datetime("0000-01-01")].containsAll([]))) && false
};
