permit(
  principal,
  action,
  resource == a::""
) when {
  true && (if ({"": false, "\0": false} has "") then false else false)
};
