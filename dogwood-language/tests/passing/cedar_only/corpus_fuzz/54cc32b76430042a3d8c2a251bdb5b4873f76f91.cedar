permit(
  principal,
  action,
  resource == a::""
) when {
  true && (if (context has D) then false else false)
};
