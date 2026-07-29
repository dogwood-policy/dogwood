forbid(
  principal,
  action,
  resource
) when {
  (true && ((if (context has "") then context else context)[""])) && false
};
