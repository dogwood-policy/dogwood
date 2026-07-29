@A("")
permit(
  principal,
  action,
  resource
) when {
  (true && ((if ([true, true, true].isEmpty()) then [] else []).isEmpty())) && false
};
