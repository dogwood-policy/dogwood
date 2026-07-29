permit(
  principal,
  action,
  resource
) when {
  ((true && (context has "")) && false) && false
};
