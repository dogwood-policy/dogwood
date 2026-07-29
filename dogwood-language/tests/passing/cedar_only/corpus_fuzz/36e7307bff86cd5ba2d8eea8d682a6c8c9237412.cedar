permit(
  principal,
  action,
  resource
) when {
  (true && ((if true then context else context)[""])) && false
};
