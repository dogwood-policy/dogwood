permit(
  principal,
  action,
  resource
) when {
  ((true && ((ip(a::"\0".L)).isMulticast())) && true) && false
};
